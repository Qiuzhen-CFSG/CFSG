module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.Factorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocalContract
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.TwoLocal.Foundations

/-!
# The translation quotient in Suzuki Lemma 14.6

Write A = closure (Z ∩ M), E = Z(T), and K = residualCommutator M t.
The nontrivial normal subgroup E/A in the two-group S/A meets its center.
Since E = AU, a representative gives u ∈ U minus identity such that the
literal coset Delta = Au is invariant under direct conjugation by S.

For H = N_G(Delta) ∩ C_G(A), evaluation at u gives the homomorphism
h ↦ h*u*h⁻¹*u⁻¹ into A, with kernel T. Thus H is a two-group and equals
S by Sylow maximality inside N_G(T). Normality of C_G(A) in M now shows
that K normalizes S. The translation image is nontrivial and K-invariant;
regularity of K on A minus identity makes evaluation surjective. The first
isomorphism theorem supplies the literal S/T ≃ A. Applying the previously
proved order reduction promotes S to an ambient Sylow two-subgroup.

These results discharge the quotient and ambient Sylow conclusions under
the original Context, LocalGeometry and TorusSemiregular inputs. They require
no centralizer embedding beyond the supplied geometry. The remaining clauses
of Lemma 14.6 belong to the enclosing assembly.

Source: GLS4, Chapter 2, Lemma 14.6, first proof paragraph,
`refs/KGroup/GLS4/Chapter2.tex`, approximately lines 2540–2560.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

private theorem fixed_coset (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    ∃ u ∈ g.U, u ≠ 1 ∧ g.S ≤ normalizer (distinguishedCoset Z M u) := by
  let A := closure (Z ∩ (M : Set G))
  let E := centerIn g.T
  have hAS : A ≤ g.S := g.A_le_P.trans (g.P_le_T.trans g.T_lt_S.le)
  have hES : E ≤ g.S := inf_le_left.trans g.T_lt_S.le
  have hSC : g.S ≤ centralizer (A : Set G) := d.S_le_distinguished_centralizer g hsemi
  let A' := A.subgroupOf g.S
  let E' := E.subgroupOf g.S
  let : A'.Normal := normal_subgroupOf_of_le_normalizer
    (hSC.trans (Subgroup.centralizer_le_normalizer _))
  let : E'.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_centerIn g.S_le_normalizer_T)
  let q : g.S →* g.S ⧸ A' := QuotientGroup.mk' A'
  let R := E'.map q
  let : R.Normal := (inferInstance : E'.Normal).map q (QuotientGroup.mk'_surjective A')
  have hR : R ≠ ⊥ := by
    obtain ⟨u, hu, hune⟩ := g.U.bot_or_exists_ne_one.resolve_left (d.U_ne_bot g)
    have huE : u ∈ E := by
      change u ∈ centerIn g.T
      rw [centerIn_eq_map_center]
      exact g.U_le_center_T hu
    intro he
    have hqu : q ⟨u, hES huE⟩ ∈ R := mem_map_of_mem q huE
    rw [he, mem_bot] at hqu
    have huA : u ∈ A := (QuotientGroup.eq_one_iff (N := A') _).mp hqu
    exact hune (disjoint_def.mp g.P_disjoint_U (g.A_le_P huA) hu)
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR
  let : Fact (IsPGroup 2 (g.S ⧸ A')) := ⟨g.S_isPGroup.to_quotient A'⟩
  obtain ⟨v, hvne, hvcentral⟩ := exists_nontrivial_center_mem_normal R (p := 2)
  obtain ⟨w, hw, hwv⟩ := v.property
  have hwE : (w : G) ∈ (center g.T).map g.T.subtype := by
    rw [← centerIn_eq_map_center]
    exact hw
  obtain ⟨a, ha, u, hu, hau⟩ := (Set.ext_iff.mp g.T_center_product (w : G)).mp hwE
  have huS : u ∈ g.S := g.T_lt_S.le (g.U_le_T hu)
  have hqu : q ⟨u, huS⟩ = (v : g.S ⧸ A') := by
    rw [← hwv]
    have hw' : w = (⟨a, hAS ha⟩ : g.S) * ⟨u, huS⟩ := Subtype.ext hau.symm
    rw [hw', map_mul]
    have hqa : q ⟨a, hAS ha⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    rw [hqa, one_mul]
  have hune : u ≠ 1 := by
    intro he
    apply hvne
    apply Subtype.ext
    rw [← hqu]
    have he' : (⟨u, huS⟩ : g.S) = 1 := Subtype.ext he
    rw [he', map_one]
    rfl
  have hmove (s : G) (hs : s ∈ g.S) : MulAut.conj s u * u⁻¹ ∈ A := by
    have hc := (mem_center_iff.mp hvcentral) (q ⟨s, hs⟩)
    rw [← hqu] at hc
    have hq : q (⟨s, hs⟩ * ⟨u, huS⟩ * (⟨s, hs⟩ : g.S)⁻¹ *
        (⟨u, huS⟩ : g.S)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := A') _).mp hq
  have hstable (s : G) (hs : s ∈ g.S) (v : G)
      (hv : v ∈ distinguishedCoset Z M u) :
      MulAut.conj s v ∈ distinguishedCoset Z M u := by
    obtain ⟨a, ha, rfl⟩ := hv
    refine ⟨a * (MulAut.conj s u * u⁻¹), A.mul_mem ha (hmove s hs), ?_⟩
    have hsa : MulAut.conj s a = a := by
      change s * a * s⁻¹ = a
      rw [← hSC hs a ha, mul_inv_cancel_right]
    rw [map_mul, hsa, mul_assoc, inv_mul_cancel_right]
  refine ⟨u, hu, hune, ?_⟩
  intro s hs
  apply mem_normalizer_iff_conj_image_eq.mpr
  apply Set.Subset.antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact hstable s hs w hw
  · intro v hv
    refine ⟨MulAut.conj s⁻¹ v, hstable s⁻¹ (g.S.inv_mem hs) v hv, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
private theorem translation_mem (H : Subgroup G) (u : G)
    (hn : H ≤ normalizer (distinguishedCoset Z M u)) (x : H) :
    MulAut.conj (x : G) u * u⁻¹ ∈ closure (Z ∩ (M : Set G)) := by
  have hu : u ∈ distinguishedCoset Z M u := ⟨1, one_mem _, (one_mul u).symm⟩
  obtain ⟨a, ha, he⟩ := (hn x.property u).mp hu
  simpa only [MulAut.conj_apply, he, mul_inv_cancel_right] using ha

private def translation (d : Context Z M z t m) (H : Subgroup G) (u : G)
    (hn : H ≤ normalizer (distinguishedCoset Z M u))
    (hc : H ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    H →* closure (Z ∩ (M : Set G)) := by
  let := d.distinguished_elementary_card.1
  refine
    { toFun := fun x => ⟨MulAut.conj (x : G) u * u⁻¹, translation_mem H u hn x⟩
      map_one' := by ext; simp
      map_mul' := ?_ }
  intro x y
  apply Subtype.ext
  have hcomm := (hc x.property _ (translation_mem H u hn y)).symm
  change (x : G) * (MulAut.conj (y : G) u * u⁻¹) =
    (MulAut.conj (y : G) u * u⁻¹) * x at hcomm
  calc
    MulAut.conj ((x * y : H) : G) u * u⁻¹ =
        (x : G) * (MulAut.conj (y : G) u * u⁻¹) * (x : G)⁻¹ *
          (MulAut.conj (x : G) u * u⁻¹) := by
      simp only [MulAut.conj_apply, coe_mul]
      group
    _ = (MulAut.conj (y : G) u * u⁻¹) * (MulAut.conj (x : G) u * u⁻¹) := by
      rw [hcomm, mul_inv_cancel_right]
    _ = _ := congrArg Subtype.val
      (mul_comm (⟨_, translation_mem H u hn y⟩ : closure (Z ∩ (M : Set G)))
        ⟨_, translation_mem H u hn x⟩)

private theorem translation_ker (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (H : Subgroup G) {u : G}
    (hu : u ∈ g.U) (hune : u ≠ 1)
    (hn : H ≤ normalizer (distinguishedCoset Z M u))
    (hc : H ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G)) :
    (translation d H u hn hc).ker = g.T.subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change MulAut.conj (x : G) u * u⁻¹ = 1 ↔ (x : G) ∈ g.T
  rw [mul_inv_eq_one, ← g.centralizer_U u hu hune]
  constructor
  · intro he
    refine ⟨hc x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg (fun v : G => v * x) he
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hh
  · rintro ⟨_, hx⟩
    change (x : G) * u * (x : G)⁻¹ = u
    rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]

private theorem translation_stabilizer_eq (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) {u : G}
    (hu : u ∈ g.U) (hune : u ≠ 1)
    (hn : g.S ≤ normalizer (distinguishedCoset Z M u)) :
    normalizer (distinguishedCoset Z M u) ⊓
      centralizer (closure (Z ∩ (M : Set G)) : Set G) = g.S := by
  let A := closure (Z ∩ (M : Set G))
  let H := normalizer (distinguishedCoset Z M u) ⊓ centralizer (A : Set G)
  have hSH : g.S ≤ H := le_inf hn (d.S_le_distinguished_centralizer g hsemi)
  let f := translation d H u inf_le_left inf_le_right
  have hker : f.ker = g.T.subgroupOf H :=
    translation_ker d g H hu hune inf_le_left inf_le_right
  have hkp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (g.S_isPGroup.to_le g.T_lt_S.le).comap_subtype
  let := d.distinguished_elementary_card.1
  have hp : IsPGroup 2 H := by
    have ht := ((IsElementaryAbelian.isPGroup 2 A).to_subgroup ⊤).comap_of_ker_isPGroup f hkp
    simpa using ht.of_equiv Subgroup.topEquiv
  have hHN : H ≤ normalizer (g.T : Set G) :=
    inf_le_left.trans (g.distinguishedCoset_normalizer_le hu hune)
  obtain ⟨V, hV⟩ := g.S_sylow
  have he : H.subgroupOf (normalizer (g.T : Set G)) = (V : Subgroup _) :=
    V.is_maximal' hp.comap_subtype (by
      intro x hx
      exact hSH (hV ▸ mem_map_of_mem (normalizer (g.T : Set G)).subtype hx))
  calc
    H = (H.subgroupOf (normalizer (g.T : Set G))).map
        (normalizer (g.T : Set G)).subtype := (map_subgroupOf_eq_of_le hHN).symm
    _ = g.S := by rw [he, hV]

private theorem translation_surjective (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) {u : G}
    (hu : u ∈ g.U) (hune : u ≠ 1)
    (hn : g.S ≤ normalizer (distinguishedCoset Z M u)) :
    Function.Surjective (translation d g.S u hn (d.S_le_distinguished_centralizer g hsemi)) := by
  let A := closure (Z ∩ (M : Set G))
  let N := normalizer (distinguishedCoset Z M u)
  have he := translation_stabilizer_eq d g hsemi hu hune hn
  have hNC : N ≤ normalizer (centralizer (A : Set G) : Set G) :=
    (d.distinguishedCoset_normalizer_le_M g hu hune).trans
      ((normal_subgroupOf_iff_le_normalizer d.distinguished_centralizer_le).mp
        d.distinguished_centralizer_normal)
  have hNS : N ≤ normalizer (g.S : Set G) := by
    rw [← he]
    exact (le_inf N.le_normalizer hNC).trans inf_normalizer_le_normalizer_inf
  let f := translation d g.S u hn (d.S_le_distinguished_centralizer g hsemi)
  have hker : f.ker = g.T.subgroupOf g.S :=
    translation_ker d g g.S hu hune hn (d.S_le_distinguished_centralizer g hsemi)
  obtain ⟨s, hs, hsT⟩ := SetLike.exists_of_lt g.T_lt_S
  let s' : g.S := ⟨s, hs⟩
  have hfa : (f s' : G) ≠ 1 := by
    intro hh
    have hf : s' ∈ f.ker := Subtype.ext hh
    rw [hker] at hf
    exact hsT hf
  intro a
  by_cases ha : a = 1
  · exact ⟨1, (map_one f).trans ha.symm⟩
  have ha1 : (a : G) ≠ 1 := fun hh => ha (Subtype.ext hh)
  obtain ⟨k, hk, _⟩ := d.torus_regular_distinguished g hsemi
    (f s').property hfa a.property ha1
  have hkN := d.torus_normalizes_distinguishedCoset g hu k.property
  have hks : MulAut.conj (k : G) s ∈ g.S := (hNS hkN s).mp hs
  refine ⟨⟨MulAut.conj (k : G) s, hks⟩, ?_⟩
  apply Subtype.ext
  change MulAut.conj (MulAut.conj (k : G) s) u * u⁻¹ = (a : G)
  rw [← hk]
  change MulAut.conj (MulAut.conj (k : G) s) u * u⁻¹ =
    MulAut.conj (k : G) (MulAut.conj s u * u⁻¹)
  have hku := d.torus_conj_U g k.property hu
  calc
    _ = MulAut.conj (MulAut.conj (k : G) s) (MulAut.conj (k : G) u) *
        (MulAut.conj (k : G) u)⁻¹ := by rw [hku]
    _ = _ := by simp only [MulAut.conj_apply]; group

/-- The actual source quotient is the full translation group of a distinguished coset. -/
public theorem Context.twoLocal_quotient_equiv (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    letI := g.T_normal_in_S
    Nonempty ((g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G))) := by
  let := g.T_normal_in_S
  obtain ⟨u, hu, hune, hn⟩ := fixed_coset d g hsemi
  let f := translation d g.S u hn (d.S_le_distinguished_centralizer g hsemi)
  have hker := translation_ker d g g.S hu hune hn
    (d.S_le_distinguished_centralizer g hsemi)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      (translation_surjective d g hsemi hu hune hn))⟩

/-- Applying the quotient construction gives Sylow maximality in the ambient group. -/
public theorem Context.twoLocal_S_sylow (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t) :
    ∃ V : Sylow 2 G, (V : Subgroup G) = g.S :=
  d.S_sylow_of_quotient_equiv g (d.twoLocal_quotient_equiv g hsemi)

end BenderSuzuki.ZD.SuzukiExclusion
