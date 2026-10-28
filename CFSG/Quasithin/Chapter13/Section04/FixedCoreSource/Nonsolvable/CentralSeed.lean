module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Parabolics
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OmegaLine
public import Theory.Representation.SylowFixedConjugation
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.Representation.BinaryPermutation.SixNaturalSylowFixed

/-!
# Recovering the full central seed from the component module

The earlier index |Z:C_Z(L)|=2 and maximal two-local uniqueness show that
an escaping component K fixes exactly the line of z in Z=Ω₁Z(T). Given the
source splitting ⟨Zᴷ⟩=U C_Z(K), the three literal module markings then bound
|Z| by four: the natural modules have Sylow fixed space of order at most
two, and the five-dimensional core has fixed space of order at most four
and already contains z. The marked V∩Z has order four, so it exhausts Z.

This proves the central-seed step from the component classification and
splitting, with the original quotient and conjugation maps. Constructing K,
its module marking, and the splitting remains with
qt-d-1341-nonsolvable-source; these are not assumed source conclusions of
13.4.1. Earlier index and local uniqueness inputs retain final discharge
with qt-d-1341-fixed-core-source. CentralSeedParabolics applies this result
to the literal 13.4.7(b–c) residual-centralizer premises.

Source: Aschbacher–Smith, 13.4.3(2), 13.4.10(4–5), pp.897 and909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V K U : Subgroup G} {D : ChosenModule T L V}

/-- The already marked four-group exhausts the full omega-center once its order is bounded by four. -/
theorem full_seed_of_card_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) ≤ 4) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hc := m.central_four_card_eq_four h structural z hz1 hzT hzout
  have he : V ⊓ omegaOneCenterAmbient (T : Subgroup G) =
      omegaOneCenterAmbient (T : Subgroup G) :=
    eq_of_le_of_card_ge inf_le_right (by rw [hc]; exact hcard)
  exact ⟨he.symm, he ▸ hc⟩

/-- A natural component with a fixed central involution gives the full order-four seed. -/
theorem full_seed_of_natural_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (U : Subgroup G) (hUT : U ≤ T)
    (hspan : omegaOneCenterAmbient (T : Subgroup G) ≤ U ⊔ zpowers z.val)
    (hbound : Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  apply full_seed_of_card_bound h structural m z hz1 hzT hzout
  have hzC : zpowers z.val ≤ centralizer (T : Set G) :=
    zpowers_le.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2
  have hZC : omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (T : Set G) :=
    fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
  have hc : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1
      (fun he => hz1 (Subtype.ext he))
  have hb := Subgroup.card_fixed_sup_le_mul_of_centralizes U (T : Subgroup G)
    (zpowers z.val) (hzC.trans (centralizer_le hUT)) hzC
  rw [hc] at hb
  exact (card_le_of_le (le_inf hspan hZC)).trans
    (hb.trans (Nat.mul_le_mul_right 2 hbound))

/-- Literal model data for the module in 13.4.10(4). In the core row the
central involution belongs to the module; in each natural row the action
uses the intrinsic central-core quotient and the actual conjugation map. -/
inductive ComponentModuleAt (DK : ChosenModule T K U) (z : G) where
  | linearThree
      (quotient : (K ⧸ centralCore K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (coordinate : U ≃* Multiplicative BinaryLinearThree.Vector)
      (equivariant : ∀ (k : K) (a : U),
        (coordinate (U.normalizerMonoidHom ⟨k.val, DK.normalizes k.property⟩ a)).toAdd =
          BinaryLinearThree.W (quotient (QuotientGroup.mk' (centralCore K) k))
            (coordinate a).toAdd)
  | naturalSix
      (quotient : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6))
      (coordinate : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
      (equivariant : ∀ (k : K) (a : U),
        (coordinate (U.normalizerMonoidHom ⟨k.val, DK.normalizes k.property⟩ a)).toAdd =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
            (quotient (QuotientGroup.mk' (centralCore K) k)) (coordinate a).toAdd)
  | coreSix (marking : CoreMarking DK) (contains : z ∈ U)

/-- Derive full seed containment from each literal module row and the source span containment. -/
theorem full_seed_of_component_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (DK : ChosenModule T K U) (marking : ComponentModuleAt DK z.val)
    (hspan : omegaOneCenterAmbient (T : Subgroup G) ≤ U ⊔ zpowers z.val) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  cases marking with
  | linearThree q e he =>
    apply full_seed_of_natural_bound h structural m z hz1 hzT hzout U DK.le_sylow hspan
    exact Representation.BinaryOffender.sylow_fixed_card_le_of_conjugation_marking T K U DK.sylow_normalizes_component DK.normalizes
      BinaryLinearThree.W (q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he 2
      BinaryLinearThree.card_sylow_natural_fixed_le_two
  | naturalSix q e he =>
    apply full_seed_of_natural_bound h structural m z hz1 hzT hzout U DK.le_sylow hspan
    exact Representation.BinaryOffender.sylow_fixed_card_le_of_conjugation_marking T K U DK.sylow_normalizes_component DK.normalizes
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))
      (q.toMonoidHom.comp (QuotientGroup.mk' (centralCore K)))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he 2
      BinaryPermutation.six_natural_sylow_fixed_card_le_two
  | coreSix mK hzU =>
    apply full_seed_of_card_bound h structural m z hz1 hzT hzout
    have hZU : omegaOneCenterAmbient (T : Subgroup G) ≤ U :=
      hspan.trans (sup_le le_rfl (zpowers_le.mpr hzU))
    have hle : omegaOneCenterAmbient (T : Subgroup G) ≤
        U ⊓ centralizer (T : Set G) :=
      le_inf hZU (fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2)
    exact (card_le_of_le hle).trans mK.sylow_fixed_card_le_four

/-- An escaping component fixes exactly the chosen involution line in the full omega-center; no containment in V is assumed. -/
theorem component_full_fixed_line
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : G) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup G) (hKz : K ≤ centralizer ({z} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) = zpowers z := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have zero (a : G) (haZ : a ∈ Z) (haL : a ∈ centralizer (L : Set G))
      (haK : a ∈ centralizer (K : Set G)) : a = 1 := by
    by_contra ha1
    apply hKM
    apply le_trans ?_ (Solvable.omega_fixed_generator_centralizer_le_normalizer
      h structural haZ haL ha1)
    exact fun k hk => mem_centralizer_singleton_iff.mpr (haK k hk)
  have hzK : z ∈ centralizer (K : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mp (hKz hk)
  have hzL : z ∉ centralizer (L : Set G) := fun hzL => hz1 (zero z hzT hzL hzK)
  have hzfix : z ∈ omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) :=
    ⟨hzT,hzK⟩
  apply le_antisymm ?_ (zpowers_le.mpr hzfix)
  intro a ha
  by_cases haL : a ∈ centralizer (L : Set G)
  · rw [zero a ha.1 haL ha.2]
    exact one_mem _
  · let F := (Z ⊓ centralizer (L : Set G)).subgroupOf Z
    have haF : (⟨a,ha.1⟩ : Z) ∉ F := fun hh => haL hh.2
    have hzF : (⟨z,hzT⟩ : Z) ∉ F := fun hh => hzL hh.2
    have hazL : a * z ∈ centralizer (L : Set G) :=
      ((F.mul_mem_iff_of_index_two hindex (a := ⟨a,ha.1⟩) (b := ⟨z,hzT⟩)).mpr
        (by simp only [haF,hzF])).2
    have haz : a * z = 1 := zero (a*z) (Z.mul_mem ha.1 hzT) hazL
      ((centralizer (K : Set G)).mul_mem ha.2 hzK)
    have hae : a = z⁻¹ := eq_inv_of_mul_eq_one_left haz
    rw [hae]
    exact inv_mem (mem_zpowers z)

/-- The actual conjugate-span splitting and model marking imply source 13.4.10(5) for the full omega-center. -/
theorem full_seed_of_component_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (DK : ChosenModule T K U) (marking : ComponentModuleAt DK z.val)
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K =
      U ⊔ (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G))) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hfix := component_full_fixed_line h structural z.val
    (fun he => hz1 (Subtype.ext he)) hzT hindex K hKz hKM
  have hspan := le_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K
  rw [hsplit,hfix] at hspan
  exact full_seed_of_component_module h structural m z hz1 hzT
    (fun hh => hKM (hKz.trans hh)) DK marking hspan

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
