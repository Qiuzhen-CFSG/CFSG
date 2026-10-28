module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement

/-!
# The original normal torus image and regular section in E.6.11

An element of M normalizing U conjugates the selected component or block
inside C_G(U). Distinct conjugates commute. The actual decomposition
V = U[V,X] then makes a distinct conjugate's entire displacement lie in U,
contrary to the escaping centralizer. Thus the original component is
normalized, and its intersection with M has normal induced image on V.
The torus complement has precisely that image.

Regular conjugation makes the moved subgroup's common fixed subgroup
trivial, so the same torus supplies every field of RegularCyclicSection.
All groups, conjugations, and automizer maps are the original embedded ones.
The component/block selection and intrinsic torus construction remain with
the separate source branches.
Source: Aschbacher–Smith, E.6.11(2), printed pp.249–250.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors Hyperplanes Hyperplanes.ComponentBalance Hyperplanes.Enlargement
open Hyperplanes.Enlargement.BlockInspection
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L X : Subgroup G}

omit [Finite G] in
/-- Conjugate a block between the corresponding actual centralizers. -/
theorem centralizerBlock_conjugate (hL : CentralizerBlock U L) (g : G) :
    CentralizerBlock (U.map (MulAut.conj g).toMonoidHom)
      (L.map (MulAut.conj g).toMonoidHom) := by
  let e := MulAut.conj g
  let C := centralizer (U : Set G)
  let C' := centralizer (U.map e.toMonoidHom : Set G)
  have he : C.map e.toMonoidHom = C' := Theory.Quasithin.map_centralizer e U
  let f : C ≃* C' := (e.subgroupMap C).trans (MulEquiv.subgroupCongr he)
  have hf : (L.subgroupOf C).map f.toMonoidHom =
      (L.map e.toMonoidHom).subgroupOf C' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, heq⟩
      exact ⟨⟨y,hL.1 hy⟩,hy,Subtype.ext heq⟩
  exact ⟨(map_mono (f := e.toMonoidHom) hL.1).trans he.le,hf ▸ hL.2.map_equiv f⟩

/-- Components and blocks have commuting distinct conjugates in the local centralizer. -/
theorem local_seed_conjugates_equal_or_commute
    (ho : pPrimeCore 2 (centralizer (U : Set G)) = ⊥)
    (hL : CentralizerComponent U L ∨ CentralizerBlock U L)
    (g : G) (hg : g ∈ normalizer (U : Set G)) :
    L = L.map (MulAut.conj g).toMonoidHom ∨
      ⁅L,L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hu : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rcases hL with hc | hb
  · have hcg := centralizerComponent_conjugate hc g
    rw [hu] at hcg
    exact centralizerComponents_equal_or_commute hc hcg
  · have hbg := centralizerBlock_conjugate hb g
    rw [hu] at hbg
    by_cases he : L = L.map (MulAut.conj g).toMonoidHom
    · exact Or.inl he
    right
    have hne : L.subgroupOf (centralizer (U : Set G)) ≠
        (L.map (MulAut.conj g).toMonoidHom).subgroupOf (centralizer (U : Set G)) := by
      intro hh
      have hm := congrArg (Subgroup.map (centralizer (U : Set G)).subtype) hh
      rw [map_subgroupOf_eq_of_le hb.1,map_subgroupOf_eq_of_le hbg.1] at hm
      exact he hm
    have hc := congrArg (Subgroup.map (centralizer (U : Set G)).subtype)
      (source_blockCommutationInput G (centralizer (U : Set G))
        (fun _ => c19Condition_of_oddCore_eq_bot ho) _ _ hb.2 hbg.2 hne)
    simpa only [map_commutator,map_subgroupOf_eq_of_le hb.1,
      map_subgroupOf_eq_of_le hbg.1,Subgroup.map_bot] using hc

/-- The original moved-space decomposition forces the selected seed to be normalized. -/
theorem seed_normalized_of_displacement
    (h : HypothesisE61 K T M V) (ho : pPrimeCore 2 (centralizer (U : Set G)) = ⊥)
    (hU : U ∈ obstructionFamily M V)
    (hL : CentralizerComponent U L ∨ CentralizerBlock U L)
    (hVL : V ≤ normalizer (L : Set G)) (hXL : X ≤ L)
    (hfixed : V ⊓ centralizer (L : Set G) = U)
    (hgen : V = U ⊔ ⁅V,X⁆) :
    M ⊓ normalizer (U : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  have hgV := h.normalizer_subspace_le hU.2.1 hU.1 hg
  have hVg : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hgV
  have hUg : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp hg.2
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases local_seed_conjugates_equal_or_commute ho hL g hg.2 with he | hc
  · exact he.symm
  have hgenG : V = U ⊔ ⁅V,X.map (MulAut.conj g).toMonoidHom⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,map_commutator,hVg,hUg] using hh
  have hXC : X.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set G) := by
    rw [commutator_comm] at hc
    exact (map_mono hXL).trans (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hmoveC : ⁅V,X.map (MulAut.conj g).toMonoidHom⁆ ≤ centralizer (L : Set G) :=
    (commutator_mono le_rfl hXC).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hVL.trans (normalizer_le_normalizer_centralizer L)))
  have hmoveU : ⁅V,X.map (MulAut.conj g).toMonoidHom⁆ ≤ U := by
    rw [← hfixed]
    exact le_inf (le_sup_right.trans hgenG.symm.le) hmoveC
  have hVU : V ≤ U := hgenG.le.trans (sup_le le_rfl hmoveU)
  exact False.elim (hU.2.2.1 ((centralizer_le hVU).trans h.centralizer_le))

/-- The actual complement image is normal in the specified local automizer. -/
theorem torus_normal_image
    (h : HypothesisE61 K T M V) (ho : pPrimeCore 2 (centralizer (U : Set G)) = ⊥)
    (hU : U ∈ obstructionFamily M V)
    (hL : CentralizerComponent U L ∨ CentralizerBlock U L)
    (hVL : V ≤ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = U)
    (hgen : V = U ⊔ ⁅V,X⁆) (n : ℕ) (hx : TorusAction M V L X n) :
    ((inducedAutomizer V X).subgroupOf
      (inducedAutomizer V (localNormalizer M V ⊓ normalizer (U : Set G)))).Normal := by
  have hLH : L ≤ centralizer (U : Set G) := hL.elim And.left And.left
  have hPN : L ⊓ M ≤ normalizer (V : Set G) :=
    component_intersection_normalizes h hU hLH
  have himage : inducedAutomizer V (L ⊓ M) = inducedAutomizer V X :=
    CommutingLifts.inducedAutomizer_eq_of_centralizing_complements
      (show L ⊓ centralizer (V : Set G) ≤ centralizer (V : Set G) from inf_le_right)
      hPN hx.complement (sup_eq_right.mpr (by rw [← hx.complement]; exact le_sup_left))
  let N := localNormalizer M V ⊓ normalizer (U : Set G)
  have hNP : N ≤ normalizer (L ⊓ M : Set G) :=
    (le_inf
      ((show N ≤ M ⊓ normalizer (U : Set G) from inf_le_inf inf_le_left le_rfl).trans
        (seed_normalized_of_displacement h ho hU hL hVL
          (hx.le_intersection.trans inf_le_left) hfixed hgen))
      ((show N ≤ M from inf_le_left.trans inf_le_left).trans M.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  have hPsub : L ⊓ M ≤ N :=
    le_inf (le_inf inf_le_right hPN)
      ((inf_le_left.trans hLH).trans (Subgroup.centralizer_le_normalizer _))
  have hpN : ((L ⊓ M).subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPsub).mpr hNP
  have hh := inducedAutomizer_normal_in hPsub
    (show N ≤ normalizer (V : Set G) from inf_le_left.trans inf_le_right) hpN
  rwa [himage] at hh


omit [Finite G] in
/-- A nontrivial regular actor fixes only the complementary fixed subgroup. -/
theorem fixedSpace_eq_of_regular_decomposition [IsMulCommutative V] [Nontrivial X]
    (hUV : U ≤ V) (hUC : U ≤ centralizer (X : Set G))
    (hgen : U ⊔ ⁅V,X⁆ = V) (hr : RegularConjugation X ⁅V,X⁆) :
    V ⊓ centralizer (X : Set G) = U := by
  apply le_antisymm _ (le_inf hUV hUC)
  intro v hv
  have hWV : ⁅V,X⁆ ≤ V :=
    (le_sup_right : ⁅V,X⁆ ≤ U ⊔ ⁅V,X⁆).trans hgen.le
  have hWN : ⁅V,X⁆ ≤ normalizer (U : Set G) :=
    (hWV.trans (V.le_centralizer.trans (Subgroup.centralizer_le hUV))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hvp : v ∈ (U : Set G) * (⁅V,X⁆ : Subgroup G) := by
    rw [← coe_mul_of_right_le_normalizer_left U ⁅V,X⁆ hWN, hgen]
    exact hv.1
  obtain ⟨u,hu,w,hw,he⟩ := hvp
  have hwC : w ∈ centralizer (X : Set G) := by
    have hh := (centralizer (X : Set G)).mul_mem
      ((centralizer (X : Set G)).inv_mem (hUC hu)) hv.2
    rw [← he] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hw1 : w = 1 := by
    by_contra hn
    obtain ⟨z,_,hz⟩ := hr.2 w hw hn w hw hn
    obtain ⟨x,hx⟩ := exists_ne (1 : X)
    have hxf : (x : G) * w * (x : G)⁻¹ = w := by
      rw [mem_centralizer_iff.mp hwC x x.property]
      simp
    have h1f : ((1 : X) : G) * w * ((1 : X) : G)⁻¹ = w := by simp
    exact hx ((hz x hxf).trans (hz 1 h1f).symm)
  simp only [hw1,mul_one] at he
  exact he ▸ hu

/-- Convert the intrinsic torus of E.6.11 to its literal regular cyclic section. -/
theorem regularSection_of_torus
    (h : HypothesisE61 K T M V) (ho : pPrimeCore 2 (centralizer (U : Set G)) = ⊥)
    (hU : U ∈ obstructionFamily M V)
    (hL : CentralizerComponent U L ∨ CentralizerBlock U L)
    (hVL : V ≤ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = U)
    (hgen : V = U ⊔ ⁅V,X⁆) (hdis : U ⊓ ⁅V,X⁆ = ⊥)
    (hr : 1 < subgroupCorank V U) (hx : TorusAction M V L X (subgroupCorank V U)) :
    RegularCyclicSection M V U X := by
  let _ := h.elementary
  have hLH : L ≤ centralizer (U : Set G) := hL.elim And.left And.left
  have hXC := hx.le_intersection.trans inf_le_left |>.trans hLH
  have hXN := hx.le_intersection.trans
    (component_intersection_normalizes h hU hLH)
  have hpow : 2 < 2 ^ subgroupCorank V U := by
    have hh := Nat.lt_two_pow_self (n := subgroupCorank V U)
    omega
  let : NeZero (2 ^ subgroupCorank V U - 1) := ⟨by omega⟩
  obtain ⟨e⟩ := hx.cyclic
  have hcard : Nat.card X = 2 ^ subgroupCorank V U - 1 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; omega)
  refine ⟨le_inf (le_inf (hx.le_intersection.trans inf_le_right) hXN) hXC,
    isCyclic_of_injective e.toMonoidHom e.injective, hcard, ?_,
    fixedSpace_eq_of_regular_decomposition hU.1 (le_centralizer_iff.mp hXC)
      hgen.symm hx.regular, hgen.symm, hdis, hx.regular.2,
    torus_normal_image h ho hU hL hVL hfixed hgen _ hx⟩
  apply le_bot_iff.mp
  intro x hxC
  exact hx.disjoint ▸ (show x ∈ (L ⊓ centralizer (V : Set G)) ⊓ X from
    ⟨⟨(hx.le_intersection hxC.1).1,hxC.2⟩,hxC.1⟩)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
