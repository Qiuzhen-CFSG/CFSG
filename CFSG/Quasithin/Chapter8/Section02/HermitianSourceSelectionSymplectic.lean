module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionCenter
public import Theory.GroupTheory.SylowImageLocalization
public import Theory.SpecificGroups.SymplecticFour.Sylow.CenterReturns

/-!
# Excluding the symplectic family on the original Hermitian orbit

If a conjugate of V returns to the original Sylow, positive weak closure
makes it centralize V. The two-conjugate fixed-space identity then makes
its conjugator normalize B = V intersect J. Sylow localization extends this
to quotient conjugators, using the original kernel J, which normalizes B.

For a symplectic quotient, both parabolics return the central Sylow image
of V to the Sylow. Since they generate, B is normal in the entire pair.
Its conjugate A consequently equals B, contradicting the nontrivial cubic
action in characteristic two. This includes Sp4(2) and does not assume
J is a two-group.

TI and the non-FF intersection bound supply the needed relative normalizer
on the actual family. Selection now requires only existence of that family;
the Suzuki torus and field-four endgame remain with the source assembly.

Source: Aschbacher–Smith E.2.13(6), p.225, and 8.2.2(5), p.715
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE ChapterE.TwoConjugate
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

private theorem returning_normalizes_B (h : TwoConjugate.Hypotheses T V M g)
    (x : X) (hc : V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X)) :
    x ∈ normalizer (B V M : Set X) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨b,hb,rfl⟩
    have hp : (MulAut.conj x) b ∈ P V M g :=
      (inferInstance : (P V M g).Normal).conj_mem b ((show B V M ≤ P V M g from le_sup_left) hb) x
    have hc' := hc (mem_map_of_mem (MulAut.conj x).toMonoidHom (show b ∈ V from hb.2))
    have hqC : q ((MulAut.conj x) b) ∈ centralizer (V.map q : Set (X ⧸ Z V g)) := by
      rintro _ ⟨v,hv,rfl⟩
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg q (hc' v hv)
    have hqB : q ((MulAut.conj x) b) ∈ (B V M).map q :=
      h.quotient_fixed_eq_B ▸ ⟨mem_map_of_mem q hp,hqC⟩
    have hh : (MulAut.conj x) b ∈ ((B V M).map q).comap q := hqB
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
      (h.Z_le_B_inf_A.trans inf_le_left)] at hh
    exact hh
  · rw [card_map_of_injective (MulAut.conj x).injective]

omit [Finite X] in
private theorem core_normalizes_B (hMN : M ≤ normalizer (V : Set X)) :
    J M ≤ normalizer (B V M : Set X) :=
  (le_inf (show J M ≤ normalizer (J M : Set X) from le_normalizer_of_normal)
    ((M.normalCore_le).trans hMN)).trans inf_normalizer_le_normalizer_inf

omit [Finite X] in
private theorem map_conj_image {Y : Type*} [Group Y] (f : X →* Y)
    (D : Subgroup X) (x : X) :
    (D.map (MulAut.conj x).toMonoidHom).map f =
      (D.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

omit [Finite X] in
private theorem compose_conj_image (D : Subgroup X) (x y : X) :
    (D.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      D.map (MulAut.conj (x*y)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply,mul_assoc]

/-- The original B is preserved by every quotient conjugator returning V
into the original quotient Sylow. Kernel conjugacy retains the literal lift. -/
theorem pair_quotient_returns_normalize
    (h : TwoConjugate.Hypotheses T V M g)
    (hMN : M ≤ normalizer (V : Set X))
    (hret : ∀ x : X, V.map (MulAut.conj x).toMonoidHom ≤ T →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X))
    {Y : Type*} [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (hk : f.ker ≤ J M) (y : Y)
    (hy : (V.map f).map (MulAut.conj y).toMonoidHom ≤ (T : Subgroup X).map f) :
    y ∈ (normalizer (B V M : Set X)).map f := by
  let := h.elementary
  obtain ⟨x,rfl⟩ := hf y
  have hm : (V.map (MulAut.conj x).toMonoidHom).map f ≤ (T : Subgroup X).map f := by
    rw [map_conj_image]
    exact hy
  obtain ⟨j,hj,hjx⟩ := T.exists_kernel_conjugate_le f
    (V.map (MulAut.conj x).toMonoidHom) ((IsElementaryAbelian.isPGroup 2 V).map _) hm
  rw [compose_conj_image] at hjx
  have hN := returning_normalizes_B h (j*x) (hret (j*x) hjx)
  have hjN := core_normalizes_B hMN (hk hj)
  exact mem_map_of_mem f (((normalizer (B V M : Set X)).mul_mem_cancel_left hjN).mp hN)

open Theory.SpecificGroups.SymplecticFour
/-- The central-Sylow symplectic alternative is incompatible with the
source returning-conjugate centralization condition. The core is not assumed
to be a two-group, and field two is included. -/
theorem pair_symplectic_excluded
    (h : TwoConjugate.Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (hMN : M ≤ normalizer (V : Set X))
    (hret : ∀ x : X, V.map (MulAut.conj x).toMonoidHom ≤ T →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (X ⧸ J M) ≃* Sp F)
    (hcenter : V.map (QuotientGroup.mk' (J M)) ≤
      (center ((T : Subgroup X).map (QuotientGroup.mk' (J M)))).map
        ((T : Subgroup X).map (QuotientGroup.mk' (J M))).subtype) : False := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (J M))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := T.mapSurjective (f := π) hπ
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (Sp F) R (unipotentSylow hF (by omega))
  let f := (MulAut.conj a).toMonoidHom.comp π
  have hf : Function.Surjective f := (MulAut.conj a).surjective.comp hπ
  have hTf : (T : Subgroup X).map f = unipotent := by
    rw [←map_map]
    exact congrArg Sylow.toSubgroup ha
  have hk : f.ker ≤ J M := by
    intro x hx
    change (MulAut.conj a) (e (QuotientGroup.mk' (J M) x)) = 1 at hx
    exact (QuotientGroup.eq_one_iff x).mp
      (e.map_eq_one_iff.mp ((MulAut.conj a).map_eq_one_iff.mp hx))
  let E := V.map f
  let N := (normalizer (B V M : Set X)).map f
  have hE : E ≤ (center (unipotent (F := F))).map unipotent.subtype := by
    let c := e.trans (MulAut.conj a)
    have hh := map_mono (f := c.toMonoidHom) hcenter
    rw [map_embeddedCenter _ _ c.injective] at hh
    have hTc : ((T : Subgroup X).map (QuotientGroup.mk' (J M))).map c.toMonoidHom = unipotent := by
      rw [map_map]
      exact hTf
    rw [hTc,map_map] at hh
    exact hh
  have hN : N = ⊤ := eq_top_of_central_sylow_returns hF hn E N hE (by
    intro y hy
    exact pair_quotient_returns_normalize h hMN hret f hf hk y (hTf ▸ hy))
  have hNB : normalizer (B V M : Set X) = ⊤ := by
    have hh := congrArg (Subgroup.comap f) hN
    change ((normalizer (B V M : Set X)).map f).comap f = (⊤ : Subgroup (Sp F)).comap f at hh
    rw [comap_map_eq,comap_top,sup_eq_left.mpr (hk.trans (core_normalizes_B hMN))] at hh
    exact hh
  have hA : A V M g = B V M := mem_normalizer_iff_map_conj_eq.mp (hNB ▸ mem_top g)
  apply h.commutator_V_A_ne_bot hproper hfit
  rw [hA]
  let := h.elementary
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (V.le_centralizer.trans (centralizer_le (show (B V M : Set X) ⊆ V from inf_le_right)))
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}

/-- The actual family cannot have a symplectic quotient when weak closure
is positive. TI and the non-FF bound supply its relative normalizer. -/
theorem family_not_symplectic_of_positive_weak_closure
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (f : Family H T M V I k) (hw : 0 < globalW V T)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ¬ SymplecticAlternative (Star M H) (Star M I)
      (starImage M I M) (starImage M I T) (starImage M I V) k := by
  intro hs
  obtain ⟨x,hx,hgen⟩ := f.generate
  let i : I := ⟨x,hx⟩
  obtain ⟨S,hS⟩ := f.sylow
  have hp := Family.twoConjugate h f S hS i hgen
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hqH := selected_quadraticRatio_gt_one M H V h.normalizer_le hq
  have hZ := family_intersection_ne_bot_of_quadraticRatio_gt_one h hchar f i hgen hqH
  have hrel := relative_normalizer I M V i.val hgen hTI hNV hZ
  have hMN : M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hVI]
    intro z hz
    exact (hrel.le ⟨hz,z.property⟩).2
  have hret : ∀ z : I, (V.subgroupOf I).map (MulAut.conj z).toMonoidHom ≤ S →
      (V.subgroupOf I).map (MulAut.conj z).toMonoidHom ≤
        centralizer (V.subgroupOf I : Set I) := by
    intro z hz
    have hh := local_conjugates_centralize I T V hVI hw z⁻¹
    simp only [inv_inv] at hh
    exact hh (hS ▸ hz)
  obtain ⟨hk,_,e,_,hc,_⟩ := hs
  have hcenter : (V.subgroupOf I).map (QuotientGroup.mk' (localCore M I)) ≤
      (center ((S : Subgroup I).map (QuotientGroup.mk' (localCore M I)))).map
        ((S : Subgroup I).map (QuotientGroup.mk' (localCore M I))).subtype := by
    rw [hS]
    exact hc
  exact pair_symplectic_excluded hp (family_actor_dimension h f hchar S hS i hgen).1
    (family_characteristic_two h f hchar) hMN hret k hk
    (GaloisField.card 2 k (by omega)) e hcenter

/-- Selection on an existing family needs no symplectic-exclusion source
premise. Every other structural clause is supplied by the checked family APIs. -/
theorem exists_selected_of_family
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (f : Family H T M V I k) (hw : 0 < globalW V T)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (i : I) (S : Sylow 2 I), Selected H T M V I k i S := by
  obtain ⟨x,hx,hgen⟩ := f.generate
  let i : I := ⟨x,hx⟩
  obtain ⟨S,hS⟩ := f.sylow
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hqH := selected_quadraticRatio_gt_one M H V h.normalizer_le hq
  have hZ := family_intersection_ne_bot_of_quadraticRatio_gt_one h hchar f i hgen hqH
  have hsp := family_not_symplectic_of_positive_weak_closure h hchar f hw hq hTI hNV
  have hr := f.classified.resolve_right hsp
  have hc := family_rank_one_core h f hr
  obtain ⟨hk,hdvd,hmodel⟩ := selected_quotient f hc hsp
  have hz := family_rank_one_center h hchar f hr i hgen hTI hNV hZ
  obtain ⟨hzcore,hncore⟩ := core_markings_of_star M I T V hc hz
    (family_borel_normalizes h f hr i hgen hTI hNV hZ)
  have hTM : T ≤ M := by
    obtain ⟨R,hR,hP,hM⟩ := h.minimal
    intro t ht
    have htm := (ChapterB.minimalParabolicMax_spec R hP).2
    rw [hR,←hM] at htm
    exact htm (show (⟨t,h.le_ambient ht⟩ : H) ∈ T.subgroupOf H from ht)
  obtain ⟨hnorm,hrank⟩ := selected_model_markings selectionModelSources M I T V k S hS hTM hmodel hzcore hncore
  refine ⟨i,S,f,hgen,hS,Family.twoConjugate h f S hS i hgen,hc,
    family_characteristic_two h f hchar,hZ,?_,hNI,?_,hk,hdvd,hmodel,hzcore,hnorm,hrank,
    selected_quadraticRatio_gt_one M I V hNI hq⟩
  · exact intersection_central I V i.val hgen
  · exact relative_normalizer I M V i.val hgen hTI hNV hZ

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
