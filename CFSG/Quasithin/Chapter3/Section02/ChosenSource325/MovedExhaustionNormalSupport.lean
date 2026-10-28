module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionThreeExclusion
public import Theory.GroupTheory.GeneralizedFitting.LayerRankOrbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.ConjugateOrbitIndexTwo

/-!
# Normal component support on the two isotypic halves

The odd-rank bound on the semisimple layer limits a moved component to
exactly two conjugates. Its actor orbit is therefore its full normal orbit.
For a centerless component the two factors form an internal direct product,
with the original conjugation and multiplication as coordinates.

On an invariant subspace moved by an entire component orbit, every component
avoids the pointwise kernel. The component dichotomy makes that kernel
centralize the whole orbit, so the restricted kernel is central. Centerless
support consequently acts faithfully. This retains central kernels for the
quasisimple branch instead of assuming its central cover trivial.

The literal Chapter12 application is in
`SeedAlternativesMovedExhaustionNormalSupport`. It uses the existing
complementary-pair movement lemma to discharge movement on both halves.
The remaining FF classification, actor movement, multiplicity exclusions,
and Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith A.3.8(3), D.3.14--18, printed pp.46,202--203.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]

/-- A moved component orbit is the full normal pair under the layer rank bound. -/
theorem moved_component_orbit_normal_pair
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (componentLayer H) ≤ 2)
    (J A : Subgroup H) (hJ : IsComponent H J)
    (hm : ¬ A ≤ normalizer (J : Set H)) :
    (componentOrbit J A).Normal ∧
      ∃ a ∈ A, a ∉ normalizer (J : Set H) ∧
        (normalizer (J : Set H)).index = 2 ∧
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
        componentOrbit J A = componentOrbit J ⊤ := by
  have hi : (normalizer (J : Set H)).index = 2 := by
    rcases hJ.normal_or_index_two_of_layer_odd_rank_le_two hr with hn | hi
    · let := hn
      exact (hm (by rw [normalizer_eq_top]; exact le_top)).elim
    · exact hi
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hm
  have he : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom := by
    apply le_antisymm
    · apply iSup_le
      intro b
      rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi
        (fun he => han (mem_normalizer_iff_map_conj_eq.mpr he)) b.val with hb | hb
      · rw [hb]; exact le_sup_left
      · rw [hb]; exact le_sup_right
    · exact sup_le (le_componentOrbit J A)
        (le_iSup (fun b : A => J.map (MulAut.conj b.val).toMonoidHom) ⟨a,ha⟩)
  have ht : componentOrbit J ⊤ = J ⊔ J.map (MulAut.conj a).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two J ⊤ (normalizer (J : Set H))
      (by simpa only [relIndex_top_right] using hi) inf_le_right (mem_top a) han
  refine ⟨?_,a,ha,han,hi,he,he.trans ht.symm⟩
  rw [he]
  exact sup_conjugate_normal_of_normalizer_index_two J hi a han

omit [Finite H] in
/-- The two actual conjugates have multiplication coordinates and trivial center. -/
theorem centerless_component_pair_coordinates
    (J : Subgroup H) (hJ : IsComponent H J) (hz : center J = ⊥)
    (a : H) (han : a ∉ normalizer (J : Set H)) :
    ∃ e : J × J ≃* (J ⊔ J.map (MulAut.conj a).toMonoidHom : Subgroup H),
      (∀ x y : J, (e (x,y) : H) = x.val * (a * y.val * a⁻¹)) ∧
      center (J ⊔ J.map (MulAut.conj a).toMonoidHom : Subgroup H) = ⊥ := by
  let J' := J.map (MulAut.conj a).toMonoidHom
  have hne : J ≠ J' := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : J ≤ centralizer (J' : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne (hJ.map_conj a) hne)
  have hd : Disjoint J J' := by
    apply disjoint_def.mpr
    intro x hx hy
    have hxc : (⟨x,hx⟩ : J) ∈ center J :=
      mem_center_iff.mpr (fun y => Subtype.ext (hc y.property x hy).symm)
    exact congrArg Subtype.val (hz.le hxc)
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting J J' hd hc
  let c : J ≃* J' := J.equivMapOfInjective _ (MulAut.conj a).injective
  let d := (MulEquiv.prodCongr (MulEquiv.refl J) c).trans e
  refine ⟨d,fun x y => he x (c y),?_⟩
  have hp : center (J × J) = ⊥ := by rw [Subgroup.center_prod,hz,bot_prod_bot]
  apply bot_unique
  intro z hz'
  apply d.symm.injective
  have hh := (centerCongr d.symm ⟨z,hz'⟩).property
  exact (hp.le hh).trans (map_one d.symm).symm

omit [Finite H] in
private theorem invariant_subspace_pointwise_kernel_normalized
    (ρ : Representation (ZMod 2) H E) (I : Submodule (ZMod 2) E)
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I) :
    A ≤ normalizer (subspaceKernel ρ I ⊤ : Set H) := by
  intro a ha
  apply mem_normalizer_iff.mpr
  intro j
  constructor
  · rintro ⟨_,hj⟩
    refine ⟨mem_top _,?_⟩
    intro v hv
    have hi : ρ a⁻¹ v ∈ I := ((subspaceStabilizer ρ I).inv_mem (hAI ha) v).mpr hv
    change ρ (a*j*a⁻¹) v = v
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hj _ hi]
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  · rintro ⟨_,hj⟩
    refine ⟨mem_top _,?_⟩
    intro v hv
    have hi : ρ a v ∈ I := (hAI ha v).mpr hv
    have hh := congrArg (ρ a⁻¹) (hj (ρ a v) hi)
    simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using hh

omit [Finite H] in
private theorem component_moves_of_moved_orbit_on_invariant
    (ρ : Representation (ZMod 2) H E) (J A : Subgroup H)
    (I : Submodule (ZMod 2) E) (hAI : A ≤ subspaceStabilizer ρ I)
    (hm : ¬ I ≤ fixedSpace ρ (componentOrbit J A)) :
    ¬ I ≤ fixedSpace ρ J := by
  intro hfix
  apply hm
  have hJ : J ≤ subspaceKernel ρ I ⊤ := by
    intro j hj
    exact ⟨mem_top _, fun v hv => hfix hv ⟨j,hj⟩⟩
  have hAJ := invariant_subspace_pointwise_kernel_normalized ρ I A hAI
  have ho := iSup_conjugates_le_of_le_normalizer J A (subspaceKernel ρ I ⊤) hJ hAJ
  intro v hv j
  exact (ho j.property).2 v hv

omit [Finite H] in
/-- The kernel on a moved invariant subspace is central in the component orbit. -/
theorem component_orbit_action_kernel_le_center
    (ρ : Representation (ZMod 2) H E) (J A : Subgroup H) (hJ : IsComponent H J)
    (I : Submodule (ZMod 2) E) (hAI : A ≤ subspaceStabilizer ρ I)
    (hXI : componentOrbit J A ≤ subspaceStabilizer ρ I)
    (hm : ¬ I ≤ fixedSpace ρ (componentOrbit J A)) :
    (subgroupActionHom ρ I (componentOrbit J A) hXI).ker ≤
      center (componentOrbit J A) := by
  let X := componentOrbit J A
  let N := subspaceKernel ρ I X
  let NX := N.subgroupOf X
  let : NX.Normal := subspaceKernel_normal ρ I X hXI
  have hJm := component_moves_of_moved_orbit_on_invariant ρ J A I hAI hm
  have hAN := invariant_subspace_pointwise_kernel_normalized ρ I A hAI
  have hcomm (a : A) : N ≤ centralizer (J.map (MulAut.conj a.val).toMonoidHom : Set H) := by
    let Ja := J.map (MulAut.conj a.val).toMonoidHom
    have hJaX : Ja ≤ X := le_iSup (fun b : A => J.map (MulAut.conj b.val).toMonoidHom) a
    have havoid : ¬ Ja.subgroupOf X ≤ NX := by
      intro hle
      apply hJm
      intro v hv j
      have hja : a.val * j.val * a.val⁻¹ ∈ Ja := mem_map_of_mem _ j.property
      have hfix := hle (show (⟨_,hJaX hja⟩ : X) ∈ Ja.subgroupOf X from hja)
      have hh : a.val * j.val * a.val⁻¹ ∈ subspaceKernel ρ I ⊤ := ⟨mem_top _,hfix.2⟩
      exact ((mem_normalizer_iff.mp (hAN a.property) j.val).mpr hh).2 v hv
    have hcentral := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (((hJ.map_conj a.val).subgroupOf hJaX).normal_dichotomy NX |>.resolve_left havoid))
    intro n hn j hj
    exact congrArg Subtype.val (hcentral (show (⟨n,hn.1⟩ : X) ∈ NX from hn)
      (⟨j,hJaX hj⟩ : X) hj)
  have hNX : N ≤ centralizer (X : Set H) := by
    apply le_centralizer_iff.mpr
    apply iSup_le
    intro a
    exact le_centralizer_iff.mp (hcomm a)
  rw [←subspaceKernel_subgroupOf_eq_ker]
  intro x hx
  exact mem_center_iff.mpr (fun y => Subtype.ext (hNX hx y.val y.property))

omit [Finite H] in
/-- A centerless component orbit acts faithfully on each invariant space it moves. -/
theorem centerless_component_orbit_faithful_on_invariant
    (ρ : Representation (ZMod 2) H E) (J A : Subgroup H) (hJ : IsComponent H J)
    (I : Submodule (ZMod 2) E) (hAI : A ≤ subspaceStabilizer ρ I)
    (hXI : componentOrbit J A ≤ subspaceStabilizer ρ I)
    (hm : ¬ I ≤ fixedSpace ρ (componentOrbit J A))
    (hz : center (componentOrbit J A) = ⊥) :
    Function.Injective (subgroupActionHom ρ I (componentOrbit J A) hXI) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique ((component_orbit_action_kernel_le_center ρ J A hJ I hAI hXI hm).trans hz.le)

omit [Finite H] in
/-- Normal support has central kernels on both complementary permuted halves;
centerless support acts faithfully on both. -/
theorem normal_component_orbit_pair_actions
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (X J A : Subgroup H) [X.Normal] (hJ : IsComponent H J)
    (hX : X = componentOrbit J A) (hXn : X ≠ ⊥)
    (I : Submodule (ZMod 2) E) (t : H) (hc : IsCompl I (I.map (ρ t)))
    (hne : I ≠ I.map (ρ t))
    (hp : ∀ g : H, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ t))
    (hAI : A ≤ subspaceStabilizer ρ I) (hXI : X ≤ subspaceStabilizer ρ I) :
    A ≤ subspaceStabilizer ρ (I.map (ρ t)) ∧
    ∃ hXIt : X ≤ subspaceStabilizer ρ (I.map (ρ t)),
      (¬ I ≤ fixedSpace ρ X) ∧ (¬ I.map (ρ t) ≤ fixedSpace ρ X) ∧
      (subgroupActionHom ρ I X hXI).ker ≤ center X ∧
      (subgroupActionHom ρ (I.map (ρ t)) X hXIt).ker ≤ center X ∧
      (center X = ⊥ → Function.Injective (subgroupActionHom ρ I X hXI) ∧
        Function.Injective (subgroupActionHom ρ (I.map (ρ t)) X hXIt)) := by
  have hsecond (Y : Subgroup H) (hY : Y ≤ subspaceStabilizer ρ I) :
      Y ≤ subspaceStabilizer ρ (I.map (ρ t)) := by
    apply le_subspaceStabilizer
    intro y hy v hv
    have hey : I.map (ρ y) = I := by
      apply le_antisymm
      · rintro _ ⟨w,hw,rfl⟩
        exact (hY hy w).mpr hw
      · intro w hw
        refine ⟨ρ y⁻¹ w, ((subspaceStabilizer ρ I).inv_mem (hY hy) w).mpr hw, ?_⟩
        simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [←pair_second_stabilized ρ I t y hne hp hey]
    exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
  have hXIt := hsecond X hXI
  obtain ⟨hIm,hItm⟩ := normal_actor_moves_pair ρ hf X hXn I t hc
  have hker (P : Submodule (ZMod 2) E) (hAP : A ≤ subspaceStabilizer ρ P)
      (hXP : X ≤ subspaceStabilizer ρ P) (hPm : ¬ P ≤ fixedSpace ρ X) :
      (subgroupActionHom ρ P X hXP).ker ≤ center X := by
    subst X
    exact component_orbit_action_kernel_le_center ρ J A hJ P hAP hXP hPm
  refine ⟨hsecond A hAI,hXIt,hIm,hItm,hker I hAI hXI hIm,
    hker _ (hsecond A hAI) hXIt hItm,?_⟩
  intro hzX
  have hfaith (P : Submodule (ZMod 2) E) (hAP : A ≤ subspaceStabilizer ρ P)
      (hXP : X ≤ subspaceStabilizer ρ P) (hPm : ¬ P ≤ fixedSpace ρ X) :
      Function.Injective (subgroupActionHom ρ P X hXP) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact bot_unique ((hker P hAP hXP hPm).trans hzX.le)
  exact ⟨hfaith I hAI hXI hIm,hfaith _ (hsecond A hAI) hXIt hItm⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
