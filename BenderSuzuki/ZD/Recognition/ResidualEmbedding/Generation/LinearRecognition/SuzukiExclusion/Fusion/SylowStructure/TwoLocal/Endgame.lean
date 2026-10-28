module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.Factorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocalContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal.Foundations
public import Theory.GroupTheory.CommutatorPreimage
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Conjugation

/-!
# The endgame of Suzuki Lemma 14.6 from its translation quotient

Write A = closure (Z ∩ M) and E = Z(T). The actual isomorphism S/T ≃ A
makes every square in S lie in T. Since E is elementary abelian, the
displacement of an element of E under S is fixed by that same element
of S. The centralizer calculation C_S(u) = T for u in U minus identity
then gives [S,E] ≤ A and Z(S) = A.

The subgroup of N_G(T) centralizing A and E/A has all its squares in
C_G(E) = T. It is a two-group containing S, hence is S by Sylow
maximality. The characteristic identities A = [T,T] and E = Z(T) make
this subgroup normal in N_G(T). Evaluation at any nonidentity u in U
has kernel T; the quotient cardinality makes its image all of A.
These full conjugation orbits and the actual centralizer-closure
identities yield N_G(T) = S(D ∩ N_G(U)).

The final theorem proves the exact TwoLocalSylowGeometry contract.
Construction of its explicit quotient-isomorphism premise remains with
the independent translation argument and the enclosing source assembly.
Source: GLS4, Chapter 2, Lemma 14.6, second and third proof paragraphs,
`refs/KGroup/GLS4/Chapter2.tex`, approximately lines 2560–2580.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

omit [Finite G] in
private theorem normalizer_center (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (((center H).map H.subtype : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_embeddedCenter H _ (MulAut.conj x).injective,
    mem_normalizer_iff_map_conj_eq.mp hx]

private theorem square_in_T (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G))))
    {s : G} (hs : s ∈ g.S) : s ^ 2 ∈ g.T := by
  let := g.T_normal_in_S
  let := d.distinguished_elementary_card.1
  obtain ⟨e⟩ := he
  let q := QuotientGroup.mk' (g.T.subgroupOf g.S)
  have hpow : (e (q ⟨s, hs⟩)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) _
  have hh : q (⟨s, hs⟩ ^ 2) = 1 := e.injective (by rw [map_pow, map_pow, map_one]; exact hpow)
  change (⟨s, hs⟩ ^ 2 : g.S) ∈ g.T.subgroupOf g.S
  exact (QuotientGroup.eq_one_iff _).mp hh

private theorem fixed_center_mem_A (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t) {s y : G} (hs : s ∈ g.S) (hsT : s ∉ g.T)
    (hy : y ∈ (center g.T).map g.T.subtype) (hsy : s * y = y * s) :
    y ∈ closure (Z ∩ (M : Set G)) := by
  obtain ⟨a, ha, v, hv, rfl⟩ := (Set.ext_iff.mp g.T_center_product y).mp hy
  have hsa := d.S_le_distinguished_centralizer g hsemi hs a ha
  have hsv : s * v = v * s := by
    apply mul_left_cancel (a := a)
    calc
      a * (s * v) = s * (a * v) := by rw [← mul_assoc, hsa, mul_assoc]
      _ = (a * v) * s := hsy
      _ = a * (v * s) := mul_assoc _ _ _
  have hv1 : v = 1 := by
    by_contra hv1
    exact hsT ((d.S_inf_centralizer_U g hsemi hv hv1) ▸
      (show s ∈ g.S ⊓ centralizer ({v} : Set G) from
        ⟨hs, mem_centralizer_singleton_iff.mpr hsv⟩))
  change a * v ∈ closure (Z ∩ (M : Set G))
  rw [hv1, mul_one]
  exact ha

omit [Finite G] in
private theorem displacement_fixed {E : Subgroup G} [IsElementaryAbelian 2 E]
    {x y : G} (hx : x ∈ normalizer (E : Set G)) (hy : y ∈ E)
    (hxx : x ^ 2 ∈ centralizer (E : Set G)) :
    x * ⁅x, y⁆ = ⁅x, y⁆ * x := by
  have hy2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy
  have hz := (hx y).mp hy
  have hz2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x * y * x⁻¹) hz
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy2)
  have hzi : (x * y * x⁻¹)⁻¹ = x * y * x⁻¹ :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hz2)
  have hcomm : (x * y * x⁻¹) * y = y * (x * y * x⁻¹) := (E.le_centralizer hz y hy).symm
  have htwice : x * (x * y * x⁻¹) * x⁻¹ = y := by
    calc
      _ = (x ^ 2) * y * (x ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = y := by rw [← hxx y hy, mul_inv_cancel_right]
  have hfix : MulAut.conj x ⁅x, y⁆ = ⁅x, y⁆ := by
    change MulAut.conj x ((x * y * x⁻¹) * y⁻¹) = (x * y * x⁻¹) * y⁻¹
    rw [map_mul, map_inv]
    change (x * (x * y * x⁻¹) * x⁻¹) * (x * y * x⁻¹)⁻¹ = _
    rw [htwice, hzi, hyi, hcomm]
  have hh := congrArg (fun v : G => v * x) hfix
  simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hh

public theorem Context.endgame_commutator_center (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))) :
    ⁅g.S, (center g.T).map g.T.subtype⁆ ≤ closure (Z ∩ (M : Set G)) := by
  let := d.T_center_elementary g
  apply commutator_le.mpr
  intro s hs y hy
  by_cases hsT : s ∈ g.T
  · have hc : y ∈ centralizer (g.T : Set G) := by
      rw [← centerIn_eq_map_center] at hy
      exact hy.2
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc s hsT)]
    exact one_mem _
  · have hn := normalizer_center g.T (g.S_le_normalizer_T hs)
    have hm : ⁅s, y⁆ ∈ (center g.T).map g.T.subtype :=
      ((center g.T).map g.T.subtype).mul_mem ((hn y).mp hy)
        (((center g.T).map g.T.subtype).inv_mem hy)
    apply fixed_center_mem_A d g hsemi hs hsT hm
    apply displacement_fixed hn hy
    rw [d.T_center_centralizer g]
    exact square_in_T d g he hs

public theorem Context.endgame_S_center (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    (center g.S).map g.S.subtype = closure (Z ∩ (M : Set G)) := by
  have hES : (center g.T).map g.T.subtype ≤ g.S := (map_subtype_le _).trans g.T_lt_S.le
  apply le_antisymm
  · intro y hy
    rw [← centerIn_eq_map_center] at hy
    have hyT : y ∈ g.T := by
      rw [← d.T_center_centralizer g]
      exact centralizer_le hES hy.2
    have hyE : y ∈ (center g.T).map g.T.subtype := by
      rw [← centerIn_eq_map_center]
      exact ⟨hyT, centralizer_le g.T_lt_S.le hy.2⟩
    obtain ⟨s, hs, hsT⟩ := SetLike.exists_of_lt g.T_lt_S
    exact fixed_center_mem_A d g hsemi hs hsT hyE (hy.2 s hs)
  · rw [← centerIn_eq_map_center]
    exact le_inf (g.A_le_P.trans (g.P_le_T.trans g.T_lt_S.le))
      (le_centralizer_iff.mp (d.S_le_distinguished_centralizer g hsemi))

public theorem Context.endgame_S_normal (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))) :
    (g.S.subgroupOf (normalizer (g.T : Set G))).Normal := by
  let A := closure (Z ∩ (M : Set G))
  let E := (center g.T).map g.T.subtype
  let N := normalizer (g.T : Set G)
  let C := centralizer (A : Set G)
  let Q := N ⊓ C
  let H := commutatorPreimage Q E A
  have hNA : N ≤ normalizer (A : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    dsimp only [A]
    rw [← d.T_commutator g, map_commutator, mem_normalizer_iff_map_conj_eq.mp hx]
  have hQA : Q ≤ normalizer (A : Set G) := inf_le_left.trans hNA
  have hHC : H ≤ C := (commutatorPreimage_le Q E A).trans inf_le_right
  have hcomm : ⁅H, E⁆ ≤ A := commutator_commutatorPreimage_le Q E A hQA
  have hSH : g.S ≤ H := le_commutatorPreimage
    (le_inf g.S_le_normalizer_T (d.S_le_distinguished_centralizer g hsemi))
    (d.endgame_commutator_center g hsemi he)
  have hH2 : IsPGroup 2 H := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    have hx2 : (x : G) ^ 2 ∈ g.T := by
      rw [← d.T_center_centralizer g]
      intro y hy
      have hcA := commutator_le.mp hcomm (x : G) x.property y hy
      let := d.distinguished_elementary_card.1
      have hc2 : ⁅(x : G), y⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hcA
      have hcx := hHC x.property _ hcA
      have hpow : ⁅(x : G) ^ 2, y⁆ = 1 := by
        rw [pow_two, commutatorElement_mul_left_eq_conj_mul, ← hcx,
          mul_inv_cancel_right, ← pow_two, hc2]
      exact (commutatorElement_eq_one_iff_mul_comm.mp hpow).symm
    obtain ⟨k, hk⟩ := (g.S_isPGroup.to_le g.T_lt_S.le).exists_pow_pow_eq_one
      ⟨(x : G) ^ 2, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hh := congrArg (fun v : g.T => (v : G)) hk
    change (x : G) ^ (2 ^ (k + 1)) = 1
    rw [pow_succ', pow_mul]
    exact hh
  obtain ⟨V, hV⟩ := d.S_sylow_of_quotient_equiv g he
  have hHS : H = g.S := by
    rw [← hV] at hSH ⊢
    exact V.is_maximal' hH2 hSH
  apply (normal_subgroupOf_iff_le_normalizer g.S_le_normalizer_T).mpr
  rw [← hHS]
  apply commutatorPreimage_normalized Q E A N hQA ?_ (normalizer_center g.T) hNA
  have hNC : N ≤ normalizer (C : Set G) :=
    (d.normalizer_T_le_M g).trans
      ((normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
        d.distinguished_centralizer_normal)
  exact (le_inf N.le_normalizer hNC).trans inf_normalizer_le_normalizer_inf

public theorem Context.endgame_U_orbits (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G))))
    {u : G} (hu : u ∈ g.U) (hu1 : u ≠ 1) (v : G) :
    (∃ s ∈ g.S, MulAut.conj s u = v) ↔
      ∃ a ∈ closure (Z ∩ (M : Set G)), v = a * u := by
  let A := closure (Z ∩ (M : Set G))
  have hc : ∀ s ∈ g.S, ⁅s, u⁆ ∈ A := fun s hs =>
    commutator_le.mp (d.endgame_commutator_center g hsemi he) s hs u (g.U_le_center_T hu)
  let f : g.S →* A :=
    { toFun := fun s => ⟨⁅(s : G), u⁆, hc s s.property⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro s r
        apply Subtype.ext
        change ⁅(s : G) * r, u⁆ = ⁅(s : G), u⁆ * ⁅(r : G), u⁆
        rw [commutatorElement_mul_left_eq_conj_mul,
          ← d.S_le_distinguished_centralizer g hsemi s.property _ (hc r r.property),
          mul_inv_cancel_right]
        let := d.distinguished_elementary_card.1
        exact (A.le_centralizer (hc r r.property) _ (hc s s.property)).symm }
  have hker : f.ker = g.T.subgroupOf g.S := by
    ext s
    change f s = 1 ↔ (s : G) ∈ g.T
    rw [← d.S_inf_centralizer_U g hsemi hu hu1]
    constructor
    · intro hh
      have hh' : ⁅(s : G), u⁆ = 1 := congrArg Subtype.val hh
      exact ⟨s.property, mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp hh')⟩
    · rintro ⟨_, hs⟩
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_singleton_iff.mp hs)
  have hsurj : Function.Surjective f := by
    apply f.surjective_of_card_ker_le_div
    rw [hker]
    apply (Nat.le_div_iff_mul_le (Nat.card_pos (α := A))).mpr
    let := g.T_normal_in_S
    obtain ⟨e⟩ := he
    have hh := (g.T.subgroupOf g.S).card_mul_index
    change Nat.card (g.T.subgroupOf g.S) * Nat.card (g.S ⧸ g.T.subgroupOf g.S) =
      Nat.card g.S at hh
    rw [Nat.card_congr e.toEquiv] at hh
    exact hh.le
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⁅s, u⁆, hc s hs, by simp [commutatorElement_def, MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨s, hs⟩ := hsurj ⟨a, ha⟩
    refine ⟨s, s.property, ?_⟩
    have hh : ⁅(s : G), u⁆ = a := congrArg Subtype.val hs
    calc
      MulAut.conj (s : G) u = ⁅(s : G), u⁆ * u := by
        simp [commutatorElement_def, MulAut.conj_apply, mul_assoc]
      _ = a * u := by rw [hh]

omit [Finite G] in
private theorem normalizer_centralizer (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp
    (normal_subgroupOf_centralizer_normalizer (K : Set G))

private theorem pair_normalizer_U_le (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    residualPairStabilizer M t ⊓ normalizer (g.U : Set G) ≤ normalizer (g.T : Set G) := by
  have hT : centralizer (closure (Z ∩ (M : Set G)) : Set G) ⊓
      centralizer (g.U : Set G) = g.T := by
    obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left (d.U_ne_bot g)
    apply le_antisymm
    · rw [← g.centralizer_U u hu hu1]
      exact inf_le_inf le_rfl (centralizer_le (Set.singleton_subset_iff.mpr hu))
    · apply le_inf
      · rw [← g.centralizer_U u hu hu1]
        exact inf_le_left
      · apply le_centralizer_iff.mpr
        intro u hu
        have hh := g.U_le_center_T hu
        rw [← centerIn_eq_map_center] at hh
        exact hh.2
  rw [← hT]
  apply le_trans ?_ inf_normalizer_le_normalizer_inf
  apply le_inf
  · exact (inf_le_left.trans inf_le_left).trans
      ((normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
        d.distinguished_centralizer_normal)
  · exact inf_le_right.trans (normalizer_centralizer g.U)

private theorem normalizes_residual_of_conj_U (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) {x u v : G}
    (hu : u ∈ g.U) (hu1 : u ≠ 1) (hv : v ∈ g.U) (hv1 : v ≠ 1)
    (hx : MulAut.conj x u = v) : x ∈ normalizer (residualGenerated M z t : Set G) := by
  let := g.U_elementary
  have huI : PFAppendixIII.IsInvolution u := by
    exact ⟨hu1, elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu⟩
  have hvI : PFAppendixIII.IsInvolution v := by
    exact ⟨hv1, elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv⟩
  have hUD := g.U_le_residual_centralizer.trans d.residual_centralizer_le_pair
  have huL := d.centralizers u (hUD hu) huI
  have hvL := d.centralizers v (hUD hv) hvI
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro y ⟨w, hw, rfl⟩
    rw [← hvL, ← hx]
    exact centralizerClosure_conj_mem d.minimal.disconnected x u (huL.symm ▸ hw)
  · rw [card_map_of_injective (MulAut.conj x).injective]

public theorem Context.endgame_normalizer_product (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))) :
    (normalizer (g.T : Set G) : Set G) = (g.S : Set G) *
      ((residualPairStabilizer M t ⊓ normalizer (g.U : Set G) : Subgroup G) : Set G) := by
  let A := closure (Z ∩ (M : Set G))
  let N := normalizer (g.T : Set G)
  have hNA : N ≤ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
    exact d.normalizer_T_le_M g
  obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left (d.U_ne_bot g)
  apply Set.Subset.antisymm
  · intro x hx
    have hxu : MulAut.conj x u ∈ (center g.T).map g.T.subtype :=
      (normalizer_center g.T hx u).mp (g.U_le_center_T hu)
    obtain ⟨a, ha, v, hv, hav⟩ := (Set.ext_iff.mp g.T_center_product _).mp hxu
    change a * v = MulAut.conj x u at hav
    have hv1 : v ≠ 1 := by
      intro hv1
      have hxA : MulAut.conj x u ∈ A := by rw [← hav, hv1, mul_one]; exact ha
      have huA : u ∈ A := (hNA hx u).mpr hxA
      exact hu1 (disjoint_def.mp g.P_disjoint_U (g.A_le_P huA) hu)
    obtain ⟨s, hs, hsu⟩ := (d.endgame_U_orbits g hsemi he hv hv1 (MulAut.conj x u)).mpr
      ⟨a, ha, hav.symm⟩
    let k := s⁻¹ * x
    have hkN : k ∈ N := N.mul_mem (N.inv_mem (g.S_le_normalizer_T hs)) hx
    have hku : MulAut.conj k u = v := by
      dsimp only [k]
      calc
        MulAut.conj (s⁻¹ * x) u = MulAut.conj s⁻¹ (MulAut.conj x u) := by
          simp only [MulAut.conj_apply]; group
        _ = MulAut.conj s⁻¹ (MulAut.conj s v) := by rw [hsu]
        _ = v := by simp [MulAut.conj_apply, mul_assoc]
    have hkL := normalizes_residual_of_conj_U d g hu hu1 hv hv1 hku
    have hkM := d.normalizer_T_le_M g hkN
    obtain ⟨p, hp, b, hb, hpb⟩ := (Set.ext_iff.mp d.point_inter_residual_normalizer k).mp ⟨hkM, hkL⟩
    change p * b = k at hpb
    have hpN := g.T.le_normalizer (g.P_le_T hp)
    have hbN : b ∈ N := by
      have hh := N.mul_mem (N.inv_mem hpN) hkN
      rw [← hpb, inv_mul_cancel_left] at hh
      exact hh
    have hbU : b ∈ normalizer (g.U : Set G) := by
      rw [g.U_eq]
      apply inf_normalizer_le_normalizer_inf
      exact ⟨hbN, normalizer_centralizer _ (d.pair_le_residual_normalizer hb)⟩
    refine ⟨s * p, g.S.mul_mem hs (g.T_lt_S.le (g.P_le_T hp)), b, ⟨hb, hbU⟩, ?_⟩
    change (s * p) * b = x
    rw [mul_assoc, hpb]
    dsimp only [k]
    exact mul_inv_cancel_left s x
  · rintro x ⟨s, hs, b, hb, rfl⟩
    exact (normalizer (g.T : Set G)).mul_mem (g.S_le_normalizer_T hs)
      (pair_normalizer_U_le d g hb)

/-- GLS4, Chapter 2, Lemma 14.6 after construction of the actual translation quotient.
The quotient producer is independent; this theorem retains its literal normality instance. -/
public theorem Context.twoLocalSylowGeometry_of_quotient (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (he : letI := g.T_normal_in_S
      Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)))) :
    TwoLocalSylowGeometry g where
  S_sylow := d.S_sylow_of_quotient_equiv g he
  S_normal := d.endgame_S_normal g hsemi he
  S_center := d.endgame_S_center g hsemi
  quotient_equiv := he
  central_mod_A := (commutator_mono le_rfl g.U_le_center_T).trans
    (d.endgame_commutator_center g hsemi he)
  normalizer_product := d.endgame_normalizer_product g hsemi he
  U_orbits := fun _ hu hu1 v => d.endgame_U_orbits g hsemi he hu hu1 v

end BenderSuzuki.ZD.SuzukiExclusion
