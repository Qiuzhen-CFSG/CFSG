module
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal
/-!
# Thompson transfer with centralizer transport

An involution can be transferred into an index-two subgroup of a Sylow
subgroup while carrying any prescribed centralizing two-subgroup into
that Sylow subgroup. Choosing a Sylow subgroup of its full centralizer
also makes the target centralizer maximal among ambient two-subgroups.

Decompose the coset space into orbits of the centralizing two-subgroup.
The Mackey formula expresses transfer as a product over these orbits.
A nontrivial orbit has even length and contributes one; fixed orbits
retain the whole centralizing subgroup. A binary character separating
all such fixed conjugates would transfer nontrivially, contradicting the
absence of a normal subgroup of index two.

The private coset decomposition adapts the existing proof in
`Theory.GroupTheory.TransferSelfNormalizer` to an arbitrary acting subgroup.
Source: GLS, No. 2, 15.13 and 15.15--16, printed pp.92--93
(`refs/KGroup/GLS2/ChapterD.tex`); the involution specialization used in
Aschbacher--Smith 14.3.33(3), printed p.1005.
-/

open scoped Pointwise BigOperators
open MulAction Subgroup
namespace MonoidHom.CentralizerOrbit
variable {G A : Type*} [Group G] [CommGroup A]
variable (H : Subgroup G)
private theorem sectionTerm_mem (r : G ⧸ H → G) (hr : ∀ q, (r q : G ⧸ H) = q)
    (g : G) (q : G ⧸ H) : (r q)⁻¹ * g * r (g⁻¹ • q) ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, hr]
  change q = g • (r (g⁻¹ • q) : G ⧸ H)
  rw [hr, smul_inv_smul]

private theorem transfer_eq_prod_section [Finite G] (φ : H →* A)
    (r : G ⧸ H → G) (hr : ∀ q, (r q : G ⧸ H) = q) (g : G)
    [Fintype (G ⧸ H)] :
    transfer φ g = ∏ q : G ⧸ H,
      φ ⟨(r q)⁻¹ * g * r (g⁻¹ • q), sectionTerm_mem H r hr g q⟩ := by
  let T : H.LeftTransversal := ⟨Set.range r, isComplement_range_left hr⟩
  rw [transfer_def φ T]
  unfold leftTransversals.diff
  dsimp only
  rw [Subsingleton.elim H.fintypeQuotientOfFiniteIndex ‹Fintype (G ⧸ H)›]
  refine Fintype.prod_congr (α := G ⧸ H) (M := A) _ _ ?_
  intro q
  congr 1
  apply Subtype.ext
  change ((T.2.leftQuotientEquiv q : G)⁻¹ *
    ((g • T).2.leftQuotientEquiv q : G)) = _
  rw [smul_apply_eq_smul_apply_inv_smul]
  simp only [T, IsComplement.leftQuotientEquiv_apply hr, smul_eq_mul, mul_assoc]

variable (R : Subgroup G)

private abbrev orbitIndex := orbitRel.Quotient R (G ⧸ H)

private noncomputable def cosetOrbitEquiv :
    G ⧸ H ≃ Σ ω : orbitIndex H R, R ⧸ stabilizer R ω.out :=
  selfEquivSigmaOrbitsQuotientStabilizer R (G ⧸ H)

private theorem cosetOrbitEquiv_symm (ω : orbitIndex H R)
    (q : R ⧸ stabilizer R ω.out) :
    (cosetOrbitEquiv H R).symm ⟨ω, q⟩ = ofQuotientStabilizer R ω.out q := rfl

private theorem cosetOrbitEquiv_symm_smul (ω : orbitIndex H R)
    (q : R ⧸ stabilizer R ω.out) (u : R) :
    (cosetOrbitEquiv H R).symm ⟨ω, u • q⟩ =
      (u : G) • (cosetOrbitEquiv H R).symm ⟨ω, q⟩ := by
  rw [cosetOrbitEquiv_symm, cosetOrbitEquiv_symm, ofQuotientStabilizer_smul]
  rfl

private noncomputable def orbitSection (q : G ⧸ H) : G :=
  (((cosetOrbitEquiv H R q).2.out : R) : G) * (cosetOrbitEquiv H R q).1.out.out

private theorem orbitSection_symm (ω : orbitIndex H R)
    (q : R ⧸ stabilizer R ω.out) :
    orbitSection H R ((cosetOrbitEquiv H R).symm ⟨ω,q⟩) =
      (q.out : G) * ω.out.out := by
  unfold orbitSection
  generalize h : (cosetOrbitEquiv H R) ((cosetOrbitEquiv H R).symm ⟨ω,q⟩) = y
  have hy : y = ⟨ω,q⟩ := h.symm.trans ((cosetOrbitEquiv H R).apply_symm_apply _)
  cases hy
  rfl

private theorem orbitSection_eq (q : G ⧸ H) :
    ((orbitSection H R q : G) : G ⧸ H) = q := by
  obtain ⟨⟨ω, s⟩, rfl⟩ := (cosetOrbitEquiv H R).symm.surjective q
  rw [orbitSection_symm, cosetOrbitEquiv_symm]
  have h : s = (s.out : R ⧸ stabilizer R ω.out) := (Quotient.out_eq' s).symm
  conv_rhs => rw [h, ofQuotientStabilizer_mk]
  exact Quotient.coe_smul_out H (s.out : G) ω.out

private noncomputable def orbitConjugate (q : G ⧸ H) : stabilizer R q →* H where
  toFun k := ⟨q.out⁻¹ * (k : R) * q.out, by
    rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq']
    change q = ((k : R) : G) • (q.out : G ⧸ H)
    rw [QuotientGroup.out_eq']
    exact k.property.symm⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [mul_assoc]

private theorem transfer_eq_prod_stabilizer [Finite G] (φ : H →* A) (u : R)
    [Fintype (orbitIndex H R)] :
    transfer φ (u : G) =
      ∏ ω : orbitIndex H R, transfer (φ.comp (orbitConjugate H R ω.out)) u := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let (ω : orbitIndex H R) : Fintype (R ⧸ stabilizer R ω.out) := Fintype.ofFinite _
  rw [transfer_eq_prod_section H φ (orbitSection H R) (orbitSection_eq H R) (u : G)]
  rw [← (cosetOrbitEquiv H R).symm.prod_comp]
  rw [Fintype.prod_sigma]
  refine Fintype.prod_congr _ _ fun ω => ?_
  rw [transfer_eq_prod_section (stabilizer R ω.out) _ Quotient.out Quotient.out_eq' u]
  refine Fintype.prod_congr _ _ fun q => ?_
  change φ _ = φ _
  congr 1
  apply Subtype.ext
  change (orbitSection H R ((cosetOrbitEquiv H R).symm ⟨ω,q⟩))⁻¹ * (u : G) *
      orbitSection H R ((u : G)⁻¹ • (cosetOrbitEquiv H R).symm ⟨ω,q⟩) =
    ω.out.out⁻¹ * (((q.out : R)⁻¹ * u * (u⁻¹ • q).out : R) : G) * ω.out.out
  rw [← Subgroup.coe_inv, ← cosetOrbitEquiv_symm_smul H R ω q u⁻¹,
    orbitSection_symm, orbitSection_symm]
  simp only [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]


private theorem transfer_eq_pow_of_centralizer_conjugates
    [Finite G] [Finite A] (φ : H →* A) (hA : Nat.card A = 2)
    (hR : IsPGroup 2 R) (u : R) (hu : u ∈ center R) (hu2 : u ^ 2 = 1)
    (a : A)
    (hrespect : ∀ g : G, ∀ hg : R.map (MulAut.conj g).toMonoidHom ≤ H,
      φ ⟨MulAut.conj g (u : G), hg (mem_map_of_mem _ u.property)⟩ = a) :
    φ.transfer (u : G) = a ^ H.index := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let : Fintype (orbitIndex H R) := Fintype.ofFinite _
  let (ω : orbitIndex H R) : Fintype (R ⧸ stabilizer R ω.out) := Fintype.ofFinite _
  have hsum : ∑ ω : orbitIndex H R, (stabilizer R ω.out).index = H.index := by
    simpa only [index_eq_card, Nat.card_eq_fintype_card, Fintype.card_sigma] using
      (Fintype.card_congr (cosetOrbitEquiv H R)).symm
  rw [transfer_eq_prod_stabilizer H R φ u]
  calc
    _ = ∏ ω : orbitIndex H R, a ^ (stabilizer R ω.out).index := by
      apply Finset.prod_congr rfl
      intro ω _
      let K := stabilizer R ω.out
      have key (k : ℕ) (v : R) (_ : v⁻¹ * u ^ k * v ∈ K) :
          v⁻¹ * u ^ k * v = u ^ k := by
        have hc : Commute (u ^ k) v := (show Commute u v from (mem_center_iff.mp hu v).symm).pow_left k
        rw [mul_assoc, hc.eq, inv_mul_cancel_left]
      rw [transfer_eq_pow _ u key]
      change φ (orbitConjugate H R ω.out ⟨u ^ K.index, _⟩) = a ^ K.index
      by_cases hk : K.index = 1
      · have htop : K = ⊤ := index_eq_one.mp hk
        have hmap : R.map (MulAut.conj ω.out.out⁻¹).toMonoidHom ≤ H := by
          rintro _ ⟨v,hv,rfl⟩
          have hvK : (⟨v,hv⟩ : R) ∈ K := htop ▸ mem_top _
          have hm := (orbitConjugate H R ω.out ⟨⟨v,hv⟩,hvK⟩).property
          change ω.out.out⁻¹ * v * ω.out.out ∈ H at hm
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hm
        simpa only [hk, pow_one, orbitConjugate, MonoidHom.coe_mk, OneHom.coe_mk,
          MulAut.conj_apply, inv_inv] using hrespect ω.out.out⁻¹ hmap
      · have hdiv : 2 ∣ K.index := by
          obtain ⟨n,hn⟩ := hR.exists_card_eq
          obtain ⟨k,_,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
            (K.index_dvd_card.trans (by rw [hn]))
          cases k with
          | zero => exact (hk (by simpa using he)).elim
          | succ k => rw [he, pow_succ]; exact dvd_mul_left _ _
        have huindex : u ^ K.index = 1 := by
          obtain ⟨n,hn⟩ := hdiv
          rw [hn,pow_mul,hu2,one_pow]
        have haindex : a ^ K.index = 1 := by
          obtain ⟨n,hn⟩ := hdiv
          rw [hn,pow_mul,show a^2=1 from hA ▸ pow_card_eq_one',one_pow]
        rw [haindex]
        have he : (⟨u ^ K.index, transfer_eq_pow_aux u key⟩ : K) = 1 := Subtype.ext huindex
        rw [he,map_one,map_one]
    _ = a ^ H.index := by rw [Finset.prod_pow_eq_pow_sum,hsum]

end MonoidHom.CentralizerOrbit

namespace Sylow
open Subgroup
/-- Transfer into an index-two subgroup while retaining a prescribed
centralizing two-subgroup of the original involution. -/
public theorem exists_isConj_mem_with_centralizer_transport
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U : Subgroup S) (hU : U.index = 2)
    (R : Subgroup G) (hR : IsPGroup 2 R)
    (u : R) (hu : u ∈ center R) (hu2 : u ^ 2 = 1) :
    ∃ g : G, ∃ hg : R.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G),
      (⟨MulAut.conj g (u : G), hg (mem_map_of_mem _ u.property)⟩ : S) ∈ U := by
  classical
  let : U.Normal := U.normal_of_index_eq_two hU
  have hcard : Nat.card (S ⧸ U) = 2 := hU
  let : IsCyclic (S ⧸ U) := isCyclic_of_prime_card hcard
  let : CommGroup (S ⧸ U) := IsCyclic.commGroup
  let φ := QuotientGroup.mk' U
  obtain ⟨a,ha1,ha⟩ := (Nat.card_eq_two_iff' (1 : S ⧸ U)).mp hcard
  by_contra! hnot
  have heval := MonoidHom.CentralizerOrbit.transfer_eq_pow_of_centralizer_conjugates
    (S : Subgroup G) R φ hcard hR u hu hu2 a (by
      intro g hg
      apply ha
      intro he
      exact hnot g hg ((QuotientGroup.eq_one_iff _).mp he))
  have hindex : φ.transfer.ker.index = 1 := by
    have hdiv : φ.transfer.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      simpa only [hcard] using card_subgroup_dvd_card φ.transfer.range
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact hone
    · exact (hno _ inferInstance htwo).elim
  have htrivial : φ.transfer (u : G) = 1 := by
    change (u : G) ∈ φ.transfer.ker
    rw [index_eq_one.mp hindex]
    trivial
  have hodd : (S : Subgroup G).index % 2 = 1 := by
    have hh := S.not_dvd_index
    omega
  have hp : a ^ (S : Subgroup G).index = a := by
    simpa only [hcard,hodd,pow_one] using (pow_mod_natCard a (S : Subgroup G).index).symm
  exact ha1 (hp.symm.trans (heval.symm.trans htrivial))

/-- Extremal Thompson transfer, with the actual conjugator transporting the
original Sylow centralizer. -/
public theorem exists_isConj_mem_with_saturated_centralizer_transport
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U : Subgroup S) (hU : U.index = 2) (x : S) (hx : orderOf x = 2) :
    ∃ (y : S) (g : G), MulAut.conj g (x : G) = (y : G) ∧ y ∈ U ∧
      (((S : Subgroup G) ⊓ centralizer ({(x : G)} : Set G)).map
        (MulAut.conj g).toMonoidHom ≤
          (S : Subgroup G) ⊓ centralizer ({(y : G)} : Set G)) ∧
      ∀ W : Subgroup G, IsPGroup 2 W →
        (S : Subgroup G) ⊓ centralizer ({(y : G)} : Set G) ≤ W →
        W ≤ centralizer ({(y : G)} : Set G) →
        W = (S : Subgroup G) ⊓ centralizer ({(y : G)} : Set G) := by
  let C := centralizer ({(x : G)} : Set G)
  let B := (S : Subgroup G) ⊓ C
  have hB : IsPGroup 2 B := S.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)
  obtain ⟨P,hBP⟩ := (hB.comap_subtype (K := C)).exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  have hRC : R ≤ C := map_subtype_le _
  have hBR : B ≤ R := by
    rw [← map_subgroupOf_eq_of_le (show B ≤ C from inf_le_right)]
    exact map_mono hBP
  have hR : IsPGroup 2 R := P.isPGroup'.map _
  have hmax (W : Subgroup G) (hp : IsPGroup 2 W) (hRW : R ≤ W) (hWC : W ≤ C) : W = R := by
    have he := P.is_maximal' (hp.comap_subtype (K := C)) (by
      intro p hp
      exact hRW (mem_map_of_mem C.subtype hp))
    have hh := congrArg (map C.subtype) he
    change (W.subgroupOf C).map C.subtype = R at hh
    rwa [map_subgroupOf_eq_of_le hWC] at hh
  have hxR : (x : G) ∈ R := hBR ⟨x.property,mem_centralizer_singleton_iff.mpr rfl⟩
  let u : R := ⟨x,hxR⟩
  have hu : u ∈ center R := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hRC a.property))
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    have hx2 : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    exact congrArg Subtype.val hx2
  obtain ⟨g,hg,hgU⟩ := S.exists_isConj_mem_with_centralizer_transport hno U hU R hR u hu hu2
  let f := MulAut.conj g
  let y : S := ⟨f x,hg (mem_map_of_mem _ hxR)⟩
  let E := R.map f.toMonoidHom
  let D := (S : Subgroup G) ⊓ centralizer ({(y : G)} : Set G)
  have hEC : E ≤ centralizer ({(y : G)} : Set G) := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f a * f x = f x * f a
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hRC ha))
  have hED : E ≤ D := le_inf hg hEC
  have hmaxE (W : Subgroup G) (hp : IsPGroup 2 W) (hEW : E ≤ W)
      (hWC : W ≤ centralizer ({(y : G)} : Set G)) : W = E := by
    have he : W.map f.symm.toMonoidHom = R := hmax _ (hp.map _) (by
      intro a ha
      exact ⟨f a,hEW (mem_map_of_mem _ ha),f.symm_apply_apply a⟩) (by
      rintro _ ⟨a,ha,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      change f (f.symm a * (x : G)) = f ((x : G) * f.symm a)
      simpa only [map_mul,f.apply_symm_apply] using mem_centralizer_singleton_iff.mp (hWC ha))
    have hh := congrArg (map f.toMonoidHom) he
    have hid : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id G := by
      ext a
      exact f.apply_symm_apply a
    simpa only [map_map,hid,map_id] using hh
  have hDE : D = E := hmaxE D (S.isPGroup'.of_injective (inclusion inf_le_left)
    (inclusion_injective _)) hED inf_le_right
  refine ⟨y,g,rfl,hgU,(map_mono hBR).trans hED,?_⟩
  intro W hp hDW hWC
  exact (hmaxE W hp (hED.trans hDW) hWC).trans hDE.symm
end Sylow
