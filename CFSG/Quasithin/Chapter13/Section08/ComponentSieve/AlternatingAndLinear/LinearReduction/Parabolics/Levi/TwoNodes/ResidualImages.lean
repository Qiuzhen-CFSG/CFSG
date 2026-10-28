module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes.Quotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.MarkedResiduals
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.ResidualImages.Actions
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The two marked residual images in the nonadjacent-node quotient

The ambient O² residual of each actual single-node parabolic maps onto A₃
in its own marked S₃ factor and trivially into the other factor. Residual
functoriality puts both coordinates in A₃. In the other block, preservation
of the retained flag cut forces square one, so that coordinate vanishes.
The explicit cubic node rotation acts nontrivially on its own block and
therefore generates its full alternating factor.

The basis and the supplied order of the two nodes are retained throughout.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the rank-two
nonadjacent-node parabolic in 13.8.25, printed pp.959–960 (PDF pp.976–977).
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
local notation "S3" => Equiv.Perm (Fin 3)

private theorem alternating_cube : ∀ a : S3, a ∈ alternatingGroup (Fin 3) → a ^ 3 = 1 := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem alternating_cases : ∀ a r : S3, r ∈ alternatingGroup (Fin 3) → r ≠ 1 →
    a ∈ alternatingGroup (Fin 3) → a = 1 ∨ a = r ∨ a = r ^ 2 := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem residual_perm_mem {G : Type*} [Group G] (f : G →* S3) {g : G}
    (hg : g ∈ pResidual 2 G) : f g ∈ alternatingGroup (Fin 3) := by
  rw [← Equiv.Perm.twoResidual_eq_alternating]
  exact map_pResidual_le 2 f (mem_map.mpr ⟨g, hg, rfl⟩)

private theorem residual_linear_eq_one {G : Type*} [Group G] (f : G →* LinearGroup 2) {g : G}
    (hg : g ∈ pResidual 2 G) (hs : f g ^ 2 = 1) : f g = 1 := by
  have hc : f g ^ 3 = 1 := linearTwoEquivSymmetricThree.injective (by
    rw [map_pow, map_one]
    exact alternating_cube _ (residual_perm_mem (linearTwoEquivSymmetricThree.toMonoidHom.comp f) hg))
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, hs, one_mul] at hc
  exact hc

private theorem node_le_pair (b : FiveBasis) (i j n : Fin 4) (hn : n = i ∨ n = j) :
    fiveParabolic b {n} ≤ fiveParabolic b {i,j} :=
  flagStabilizer_antitone b (Set.compl_subset_compl.mpr
    (Set.singleton_subset_iff.mpr (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hn)))

private theorem residual_other_action (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n m : Fin 4)
    (hn : n = i ∨ n = j) (hm : m = i ∨ m = j) (hnm : n ≠ m)
    (g : fiveParabolic b {n}) (hg : g ∈ pResidual 2 (fiveParabolic b {n})) :
    nodeLinearAction b i j h m hm (inclusion (node_le_pair b i j n hn) g) = 1 := by
  apply residual_linear_eq_one
    ((nodeLinearAction b i j h m hm).comp (inclusion (node_le_pair b i j n hn))) hg
  apply linearTwo_square_of_entry_zero
  exact nodeLinearAction_entry_zero b i j h m hm
    (inclusion (node_le_pair b i j n hn) g)
    ((mem_flagStabilizer_iff_maps b ({n} : Set (Fin 4))ᶜ g.val).mp g.property m
      (by simpa using hnm.symm))

private theorem residual_image_properties (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j)
    {x : S3 × S3}
    (hx : x ∈ ((fiveNodeResidual b n).subgroupOf (fiveParabolic b {i,j})).map
      (fiveTwoNodeBlockAction b i j h)) :
    x.1 ∈ alternatingGroup (Fin 3) ∧ x.2 ∈ alternatingGroup (Fin 3) ∧
      (n ≠ i → x.1 = 1) ∧ (n ≠ j → x.2 = 1) := by
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hx
  obtain ⟨y, hy, hyEq⟩ := mem_map.mp hg
  have he : g = inclusion (node_le_pair b i j n hn) y := Subtype.ext hyEq.symm
  subst g
  let f := (fiveTwoNodeBlockAction b i j h).comp (inclusion (node_le_pair b i j n hn))
  refine ⟨residual_perm_mem ((MonoidHom.fst S3 S3).comp f) hy,
    residual_perm_mem ((MonoidHom.snd S3 S3).comp f) hy, ?_, ?_⟩
  · intro hni
    change linearTwoEquivSymmetricThree (nodeLinearAction b i j h i (Or.inl rfl)
      (inclusion (node_le_pair b i j n hn) y)) = 1
    rw [residual_other_action b i j h n i hn (Or.inl rfl) hni y hy, map_one]
  · intro hnj
    change linearTwoEquivSymmetricThree (nodeLinearAction b i j h j (Or.inr rfl)
      (inclusion (node_le_pair b i j n hn) y)) = 1
    rw [residual_other_action b i j h n j hn (Or.inr rfl) hnj y hy, map_one]

private theorem rotation_action_ne_one (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (n : Fin 4) (hn : n = i ∨ n = j) :
    nodeLinearAction b i j h n hn
      ⟨fiveNodeRotation b n, node_le_pair b i j n hn (fiveNodeRotation_mem b n)⟩ ≠ 1 := by
  intro he
  have hf := congrFun (LinearEquiv.congr_fun he (![1,0] : Space 2)) 1
  rw [nodeLinearAction_apply] at hf
  simp only [nodeIndexEquiv_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero] at hf
  change b.equivFun (fiveNodeRotation b n (b n.castSucc)) n.succ = 0 at hf
  rw [fiveNodeRotation_apply_left] at hf
  simp at hf

private theorem alt_prod_bot_le (H : Subgroup (S3 × S3)) (r : S3)
    (hr : (r,1) ∈ H) (ha : r ∈ alternatingGroup (Fin 3)) (hne : r ≠ 1) :
    (alternatingGroup (Fin 3)).prod ⊥ ≤ H := by
  rintro ⟨a,c⟩ ⟨ha', hc⟩
  change c = 1 at hc
  subst c
  rcases alternating_cases a r ha hne ha' with he | he | he
  · subst a; exact H.one_mem
  · subst a; exact hr
  · subst a; simpa using H.pow_mem hr 2

private theorem bot_prod_alt_le (H : Subgroup (S3 × S3)) (r : S3)
    (hr : (1,r) ∈ H) (ha : r ∈ alternatingGroup (Fin 3)) (hne : r ≠ 1) :
    (⊥ : Subgroup S3).prod (alternatingGroup (Fin 3)) ≤ H := by
  rintro ⟨c,a⟩ ⟨hc, ha'⟩
  change c = 1 at hc
  subst c
  rcases alternating_cases a r ha hne ha' with he | he | he
  · subst a; exact H.one_mem
  · subst a; exact hr
  · subst a; simpa using H.pow_mem hr 2

/-- The first node residual maps onto exactly the marked first alternating factor. -/
theorem fiveNodeResidual_map_twoNodeBlockAction_first (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    ((fiveNodeResidual b i).subgroupOf (fiveParabolic b {i,j})).map
      (fiveTwoNodeBlockAction b i j h) = (alternatingGroup (Fin 3)).prod ⊥ := by
  have hij : i ≠ j := by intro he; subst j; omega
  let H := ((fiveNodeResidual b i).subgroupOf (fiveParabolic b {i,j})).map
    (fiveTwoNodeBlockAction b i j h)
  have hle : H ≤ (alternatingGroup (Fin 3)).prod ⊥ := by
    intro x hx
    have hp := residual_image_properties b i j h i (Or.inl rfl) hx
    exact ⟨hp.1, hp.2.2.2 hij⟩
  apply le_antisymm hle
  let g : fiveParabolic b {i,j} :=
    ⟨fiveNodeRotation b i, node_le_pair b i j i (Or.inl rfl) (fiveNodeRotation_mem b i)⟩
  have hg : fiveTwoNodeBlockAction b i j h g ∈ H :=
    mem_map.mpr ⟨g, fiveNodeRotation_mem_residual b i, rfl⟩
  have hp := hle hg
  have hr : ((fiveTwoNodeBlockAction b i j h g).1, 1) ∈ H := by
    have he : ((fiveTwoNodeBlockAction b i j h g).1, 1) =
        fiveTwoNodeBlockAction b i j h g := Prod.ext rfl hp.2.symm
    rw [he]
    exact hg
  apply alt_prod_bot_le H _ hr hp.1
  change linearTwoEquivSymmetricThree (nodeLinearAction b i j h i (Or.inl rfl) g) ≠ 1
  rw [ne_eq, linearTwoEquivSymmetricThree.map_eq_one_iff]
  exact rotation_action_ne_one b i j h i (Or.inl rfl)

/-- The second node residual maps onto exactly the marked second alternating factor. -/
theorem fiveNodeResidual_map_twoNodeBlockAction_second (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    ((fiveNodeResidual b j).subgroupOf (fiveParabolic b {i,j})).map
      (fiveTwoNodeBlockAction b i j h) =
        (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
  have hji : j ≠ i := by intro he; subst j; omega
  let H := ((fiveNodeResidual b j).subgroupOf (fiveParabolic b {i,j})).map
    (fiveTwoNodeBlockAction b i j h)
  have hle : H ≤ (⊥ : Subgroup S3).prod (alternatingGroup (Fin 3)) := by
    intro x hx
    have hp := residual_image_properties b i j h j (Or.inr rfl) hx
    exact ⟨hp.2.2.1 hji, hp.2.1⟩
  apply le_antisymm hle
  let g : fiveParabolic b {i,j} :=
    ⟨fiveNodeRotation b j, node_le_pair b i j j (Or.inr rfl) (fiveNodeRotation_mem b j)⟩
  have hg : fiveTwoNodeBlockAction b i j h g ∈ H :=
    mem_map.mpr ⟨g, fiveNodeRotation_mem_residual b j, rfl⟩
  have hp := hle hg
  have hr : (1, (fiveTwoNodeBlockAction b i j h g).2) ∈ H := by
    have he : (1, (fiveTwoNodeBlockAction b i j h g).2) =
        fiveTwoNodeBlockAction b i j h g := Prod.ext hp.1.symm rfl
    rw [he]
    exact hg
  apply bot_prod_alt_le H _ hr hp.2
  change linearTwoEquivSymmetricThree (nodeLinearAction b i j h j (Or.inr rfl) g) ≠ 1
  rw [ne_eq, linearTwoEquivSymmetricThree.map_eq_one_iff]
  exact rotation_action_ne_one b i j h j (Or.inr rfl)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
