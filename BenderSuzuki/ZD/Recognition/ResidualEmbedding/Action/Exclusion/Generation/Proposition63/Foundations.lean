module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary

/-!
# Distinguished closure and residual for Proposition 6.3

Lemma 3.10 places `M° = ⟨Z ∩ M⟩` in `L = ⟨z,t,[O₂′(D),t]⟩`.
Four-group coprime action then puts the odd core of `L` in the actual pair
stabilizer. The subgroup `Y = O²(M°)` is normal in `M`, contains the odd
inverted elements, and sends the distinguished involutions into the two-core
of `M/Y`. No oddness of `D` or ambient strong embedding is assumed.

Source: GLS, Volume 4, Chapter 2, Lemmas 3.10, 3.13 and Proposition 6.3,
`refs/KGroup/GLS4/Chapter2.tex`, lines 990–1023.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem distinguished_reflection (h : IsProductDisconnected Z M)
    {u z : G} (hu : u ∈ Z) (hz : z ∈ Z) (n : ℕ) : (u * z) ^ n * z ∈ Z := by
  have zi := (h.involutions z hz).inv_eq_self
  have ui := (h.involutions u hu).inv_eq_self
  have zz : z * z = 1 := by simpa [pow_two] using (h.involutions z hz).sq_eq_one
  have hmove : z * (u * z)⁻¹ = (u * z) * z := by
    rw [mul_inv_rev, zi, ui, ← mul_assoc, zz, one_mul, mul_assoc, zz, mul_one]
  induction n using Nat.twoStepInduction with
  | zero => simpa using hz
  | one => simpa [pow_one, mul_assoc, zz] using hu
  | more n hn _ =>
    have he : (u * z) ^ (n + 2) * z = MulAut.conj (u * z) ((u * z) ^ n * z) := by
      symm
      change (u * z) * ((u * z) ^ n * z) * (u * z)⁻¹ = _
      calc
        _ = (u * z) * ((u * z) ^ n * (z * (u * z)⁻¹)) := by group
        _ = (u * z) * ((u * z) ^ n * ((u * z) * z)) := by rw [hmove]
        _ = (u * z) ^ (n + 2) * z := by rw [pow_succ, pow_succ']; group
    rw [he]
    exact h.invariant _ _ hn

/-- The distinguished conjugator in Lemma 3.2(b). -/
private theorem prop63_distinguished_conjugator (h : IsProductDisconnected Z M)
    {z u : G} (hz : z ∈ Z) (hzM : z ∈ M) (hu : u ∈ Z) (huM : u ∉ M) :
    ∃ t ∈ Z, MulAut.conj t z = u := by
  have hodd : Odd (orderOf (u * z)) := by
    rw [show u * z = (z * u)⁻¹ by rw [mul_inv_rev, (h.involutions z hz).inv_eq_self, (h.involutions u hu).inv_eq_self], orderOf_inv]
    exact productDisconnected_odd_orderOf_mul h hz hu huM (Or.inl hzM)
  obtain ⟨a, ha⟩ := hodd
  have zi := (h.involutions z hz).inv_eq_self
  have ui := (h.involutions u hu).inv_eq_self
  have zz : z * z = 1 := by simpa [pow_two] using (h.involutions z hz).sq_eq_one
  have hsem : SemiconjBy z (u * z)⁻¹ (u * z) := by
    change z * (u * z)⁻¹ = (u * z) * z
    rw [mul_inv_rev, zi, ui, ← mul_assoc, zz, one_mul, mul_assoc, zz, mul_one]
  have he : (u * z) ^ (a + 1) * z * ((u * z) ^ (a + 1))⁻¹ = u := by
    have hexp : (a + 1) + (a + 1) = orderOf (u * z) + 1 := by omega
    calc
      _ = (u * z) ^ (a + 1) * ((u * z) ^ (a + 1) * z) := by
        rw [← inv_pow, mul_assoc, (hsem.pow_right (a + 1)).eq]
      _ = (u * z) ^ (orderOf (u * z) + 1) * z := by
        rw [← mul_assoc, ← pow_add, hexp]
      _ = u := by rw [pow_succ, pow_orderOf_eq_one, one_mul, mul_assoc, zz, mul_one]
  refine ⟨(u * z) ^ (a + 1) * z, distinguished_reflection h hu hz _, ?_⟩
  change ((u * z) ^ (a + 1) * z) * z * ((u * z) ^ (a + 1) * z)⁻¹ = u
  simpa only [mul_inv_rev, zi, mul_assoc, zz, one_mul] using he


omit [Finite G] in
private theorem pow_two_mem_iff_of_odd_order (H : Subgroup G) {x : G}
    (hx : Odd (orderOf x)) : x ^ 2 ∈ H ↔ x ∈ H := by
  constructor
  · intro hh
    obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime
      (x := x) (n := 2) hx.coprime_two_left
    rw [← hn]
    exact H.pow_mem hh n
  · exact fun hh => H.pow_mem hh 2

/-- The distinguished generators of M lie in the odd-core residual subgroup.
The pair stabilizer is not assumed odd. -/
public theorem prop63_distinguishedClosure_le_residualGenerated
    (h : IsProductDisconnected Z M) (hs : ActionSectionThree Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    Subgroup.closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t := by
  let D := residualPairStabilizer M t
  let O := corollary64OddCore D
  let L := residualGenerated M z t
  have ti := h.involutions t ht
  have htmove : t • (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    intro he
    apply htM
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr he
  have hDeq : D = MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
      MulAction.stabilizer G (t • (QuotientGroup.mk 1 : G ⧸ M)) := by
    rw [baseCoset_stabilizer]
    change M ⊓ rightConjugate M t = M ⊓ _
    congr 1
    simpa [MulAction.Quotient.smul_mk, smul_eq_mul, ti.inv_eq_self] using
      (conjugateCoset_stabilizer M t).symm
  have hcomm : ⁅D, Subgroup.zpowers t⁆ ≤ O :=
    hs.swapping_core t ht (QuotientGroup.mk 1) htmove D
      hDeq.le (inf_rightConjugate_mem_normalizer_of_isInvolution M ti)
  apply (Subgroup.closure_le _).mpr
  intro y hy
  have hu : MulAut.conj t z ∈ Z := h.invariant t z hz
  have huM : MulAut.conj t z ∉ M := fun hm =>
    htM ((h.conjugate_mem_iff z hz hzM t).mp hm)
  obtain ⟨s, hsZ, hsy⟩ := prop63_distinguished_conjugator h hy.1 hy.2 hu huM
  have si := h.involutions s hsZ
  let k := s * t
  have hkz : MulAut.conj k z = y := by
    calc
      MulAut.conj k z = MulAut.conj s (MulAut.conj t z) := by
        simp only [k, MulAut.conj_apply]; group
      _ = MulAut.conj s (MulAut.conj s y) := by rw [hsy]
      _ = y := by
        change s * (s * y * s⁻¹) * s⁻¹ = y
        rw [si.inv_eq_self]
        calc
          s * (s * y * s) * s = (s * s) * y * (s * s) := by group
          _ = y := by rw [show s * s = 1 by simpa [pow_two] using si.sq_eq_one]; simp
  have hkM : k ∈ M := (h.conjugate_mem_iff z hz hzM k).mp (hkz ▸ hy.2)
  have hkInv : t * k * t⁻¹ = k⁻¹ := by
    simp [k, ti.inv_eq_self, si.inv_eq_self, mul_assoc,
      show t * t = 1 by simpa [pow_two] using ti.sq_eq_one]
  have hkD : k ∈ D := by
    refine ⟨hkM, ?_⟩
    change k ∈ rightConjugate M t
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨k⁻¹, M.inv_mem hkM, ?_⟩
    change t⁻¹ * k⁻¹ * (t⁻¹)⁻¹ = k
    simpa only [mul_inv_rev, inv_inv, ti.inv_eq_self, mul_assoc] using
      congrArg Inv.inv hkInv
  have hkodd : Odd (orderOf k) :=
    productDisconnected_odd_orderOf_mul h hsZ ht htM (Or.inr hkM)
  have hkcomm : ⁅k, t⁆ = k ^ 2 := by
    have hi := congrArg Inv.inv hkInv
    have hi' : t * k⁻¹ * t⁻¹ = k := by simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi
    rw [commutatorElement_def]
    calc
      k * t * k⁻¹ * t⁻¹ = k * (t * k⁻¹ * t⁻¹) := by group
      _ = k ^ 2 := by rw [hi', pow_two]
  have hkO : k ∈ O := (pow_two_mem_iff_of_odd_order O hkodd).mp (by
    rw [← hkcomm]
    exact hcomm (Subgroup.commutator_mem_commutator hkD (Subgroup.mem_zpowers t)))
  have hkC : k ∈ ⁅O, Subgroup.zpowers t⁆ :=
    (pow_two_mem_iff_of_odd_order _ hkodd).mp (by
      rw [← hkcomm]
      exact Subgroup.commutator_mem_commutator hkO (Subgroup.mem_zpowers t))
  have hkL : k ∈ L := (show ⁅O, Subgroup.zpowers t⁆ ≤ L from le_sup_right) hkC
  have hzL : z ∈ L :=
    (show Subgroup.zpowers z ≤ L from le_sup_left.trans le_sup_left) (Subgroup.mem_zpowers z)
  rw [← hkz]
  exact L.mul_mem (L.mul_mem hkL hzL) (L.inv_mem hkL)

/-- The distinguished closure inside the base stabilizer, not its full
involution core. -/
@[expose] public def prop63Core (Z : Set G) (M : Subgroup G) : Subgroup M :=
  Subgroup.closure (M.subtype ⁻¹' Z)

/-- The source residual `Y = O²(M°)`, regarded as a subgroup of `M`. -/
@[expose] public def prop63Residual (Z : Set G) (M : Subgroup G) : Subgroup M :=
  (External.hallPResidual 2 (prop63Core Z M)).map (prop63Core Z M).subtype

omit [Finite G] in
/-- The internal and ambient conventions for the distinguished closure agree. -/
public theorem prop63Core_map :
    (prop63Core Z M).map M.subtype = Subgroup.closure (Z ∩ (M : Set G)) := by
  rw [prop63Core, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro hx
    exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩

omit [Finite G] in
/-- Relative normality of `M°` in `M`. -/
public theorem prop63Core_normal (h : IsProductDisconnected Z M) :
    (prop63Core Z M).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro g _ z hz
  apply Subgroup.subset_closure
  exact h.invariant g z hz

omit [Finite G] in
/-- Characteristicity of the residual gives normality in `M`. -/
public theorem prop63Residual_normal (h : IsProductDisconnected Z M) :
    (prop63Residual Z M).Normal := by
  let _ := prop63Core_normal h
  exact ConjAct.normal_of_characteristic_of_normal

/-- Lemma 3.13 and relative normality put the odd core of `L` in the
actual pair stabilizer, even when that stabilizer has even order. -/
public theorem prop63_oddCore_le_pairStabilizer
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hs : ActionSectionThree Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M) :
    (twoPrimeCore (residualGenerated M z t)).map (residualGenerated M z t).subtype ≤
      residualPairStabilizer M t := by
  let L := residualGenerated M z t
  let O := (twoPrimeCore L).map L.subtype
  have hAL := prop63_distinguishedClosure_le_residualGenerated h.disconnected hs hz hzM ht htM
  have hOM : O ≤ M := oddCore_le_of_distinguishedClosure_le h r L hAL
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  have hOsub : O.subgroupOf L = twoPrimeCore L :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hOnormal : (O.subgroupOf L).Normal := by rw [hOsub]; infer_instance
  have hLnorm : L ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOL).mp hOnormal
  have htL : t ∈ L :=
    (show Subgroup.zpowers t ≤ L from le_sup_right.trans le_sup_left) (Subgroup.mem_zpowers t)
  have ti := h.disconnected.involutions t ht
  refine le_inf hOM ?_
  intro x hx
  have hxt : rightConjugateElem x t ∈ O := by
    simpa [rightConjugateElem, ti.inv_eq_self] using
      (Subgroup.mem_normalizer_iff.mp (hLnorm htL) x).1 hx
  have hh := rightConjugateElem_mem_rightConjugate (g := t) (hOM hxt)
  simpa [rightConjugateElem_rightConjugateElem ti.inv_eq_self] using hh

/-- Transfer of the induction output to the odd core of the pair stabilizer.
Only `Y` is normal in `M`; the pair stabilizer is not declared normal there. -/
public theorem prop63_residual_le_pairOddCore_of_le_oddCore
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hs : ActionSectionThree Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hY : (prop63Residual Z M).map M.subtype ≤
      (twoPrimeCore (residualGenerated M z t)).map (residualGenerated M z t).subtype) :
    (prop63Residual Z M).map M.subtype ≤ corollary64OddCore (residualPairStabilizer M t) := by
  let L := residualGenerated M z t
  let D := residualPairStabilizer M t
  let Y := prop63Residual Z M
  let YX := Y.map M.subtype
  let YD := Y.comap (Subgroup.inclusion (show D ≤ M from inf_le_left))
  have hYD : YX ≤ D := hY.trans (prop63_oddCore_le_pairStabilizer h r hs hz hzM ht htM)
  have hYDmap : YD.map D.subtype = YX := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, x.property.1⟩, hx, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨⟨y, hYD (Subgroup.mem_map_of_mem M.subtype hy)⟩, hy, rfl⟩
  let _ : Y.Normal := prop63Residual_normal h.disconnected
  have hYDnormal : YD.Normal := inferInstance
  have hcop : Nat.Coprime 2 (Nat.card YD) := by
    have hdiv := Subgroup.card_dvd_of_le hY
    have heq : Nat.card YD = Nat.card YX := by
      rw [← hYDmap, Subgroup.card_map_of_injective D.subtype_injective]
    rw [heq]
    apply Nat.Coprime.of_dvd_right hdiv
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcore : YD ≤ twoPrimeCore D := le_sSup ⟨hYDnormal, hcop⟩
  change YX ≤ corollary64OddCore D
  rw [← hYDmap]
  exact Subgroup.map_mono hcore

omit [Finite G] in
/-- Odd-order elements inverted by a distinguished involution of `M` lie in
`Y`. The square lies in `M°` because it is a product of two distinguished
conjugates, and odd order allows extraction of its square root. -/
public theorem prop63_mem_residual_of_inverted
    (h : IsProductDisconnected Z M) {x z : G}
    (hxM : x ∈ M) (hxodd : Odd (orderOf x)) (hz : z ∈ Z) (hzM : z ∈ M)
    (hinv : z * x * z⁻¹ = x⁻¹) :
    (⟨x, hxM⟩ : M) ∈ prop63Residual Z M := by
  let C := prop63Core Z M
  let xM : M := ⟨x, hxM⟩
  let zM : M := ⟨z, hzM⟩
  have hzC : zM ∈ C := Subgroup.subset_closure hz
  have hconjC : xM * zM * xM⁻¹ ∈ C :=
    Subgroup.subset_closure (h.invariant x z hz)
  have hsq : xM ^ 2 ∈ C := by
    have he : (xM * zM * xM⁻¹) * zM⁻¹ = xM ^ 2 := by
      apply Subtype.ext
      change x * z * x⁻¹ * z⁻¹ = x ^ 2
      have hi : z * x⁻¹ * z⁻¹ = x := by
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hinv
      calc
        x * z * x⁻¹ * z⁻¹ = x * (z * x⁻¹ * z⁻¹) := by group
        _ = x ^ 2 := by rw [hi, pow_two]
    rw [← he]
    exact C.mul_mem hconjC (C.inv_mem hzC)
  have hxModd : Odd (orderOf xM) := by simpa [xM] using hxodd
  have hxC := (pow_two_mem_iff_of_odd_order C hxModd).mp hsq
  let xc : C := ⟨xM, hxC⟩
  have hxcodd : Odd (orderOf xc) := by simpa [xc] using hxModd
  exact Subgroup.mem_map.mpr ⟨xc, Subgroup.subset_closure hxcodd.coprime_two_left, rfl⟩

/-- The image of a distinguished involution of `M` in `M / O²(M°)` belongs to the
normal `2`-core of the quotient. The printed `O₂′` at this step of Proposition
6.3 is corrected to `O₂`: the quotient of `M°` by its two-residual is a two-group. -/
public theorem prop63_image_mem_twoCore
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {z : X}
    (h : IsProductDisconnected Z M) (hzM : z ∈ M) (hz : z ∈ Z) :
    letI := prop63Residual_normal h
    QuotientGroup.mk' (prop63Residual Z M) ⟨z, hzM⟩ ∈
      pCore 2 (M ⧸ prop63Residual Z M) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup M := prop63Core Z M
  let Y : Subgroup M := prop63Residual Z M
  let _ : (prop63Core Z M).Normal := prop63Core_normal h
  let _ : Y.Normal := prop63Residual_normal h
  let q : M →* M ⧸ Y := QuotientGroup.mk' Y
  let H : Subgroup K := External.hallPResidual 2 K
  let qK : K →* M ⧸ Y := q.comp K.subtype
  have hHker : H ≤ qK.ker := by
    intro x hxH
    apply (QuotientGroup.eq_one_iff (N := Y) (x : M)).mpr
    dsimp [Y, prop63Residual, H, K]
    exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  let : H.Normal := External.hallPResidual_normal 2 K
  let f : (K ⧸ H) →* (M ⧸ Y) :=
    QuotientGroup.lift H qK hHker
  have hquot : IsPGroup 2 (K ⧸ H) :=
    External.hallPResidual_quotient_isPGroup 2
  have hfrangeP : IsPGroup 2 f.range :=
    hquot.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfrange : f.range = K.map q := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨a, rfl⟩
      refine QuotientGroup.induction_on a ?_
      intro x
      exact Subgroup.mem_map.mpr ⟨x, x.property, by simp [f, qK]⟩
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxK, rfl⟩
      refine ⟨QuotientGroup.mk' H ⟨x, hxK⟩, ?_⟩
      simp [f, qK]
  have hC : IsPGroup 2 (K.map q) := by
    rw [← hfrange]
    exact hfrangeP
  have hCnormal : (K.map q).Normal := by
    exact Subgroup.Normal.map (inferInstance : K.Normal) q
      (QuotientGroup.mk'_surjective Y)
  have hCcore : K.map q ≤ pCore 2 (M ⧸ Y) := by
    exact le_sSup ⟨hCnormal, hC⟩
  have hzK : (⟨z, hzM⟩ : M) ∈ K := by
    change (⟨z, hzM⟩ : M) ∈ prop63Core Z M
    exact Subgroup.subset_closure hz
  have hmemC : q ⟨z, hzM⟩ ∈ K.map q := by
    exact Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, hzK, rfl⟩
  exact hCcore hmemC


end BenderSuzuki.ZD
