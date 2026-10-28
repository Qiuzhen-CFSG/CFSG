module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingPair
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Theory.LinearAlgebra.RankOneInvariantPairSwap

/-!
# Excluding the imprimitive orthogonal two-plane alternative

An involution interchanging two orthogonal summands pairs every vector
orthogonally with its image. In the central-root plane, such an element lies
on the short-root axis. The genuine diagram-moving actor therefore supplies
a commuting long-root element. Its displacement has rank one: it cannot
interchange two-dimensional summands, nor commute with their interchange
while preserving both. Thus V fixes each summand. Conjugacy gives the same
conclusion for its opposite, contradicting the pair's F-linear irreducibility.

This proves the imprimitive exclusion in Aschbacher--Smith E.2.7, printed
p.220, on the literal moving-actor pair. It does not assume a root in V and
is independent of the still-needed G.4.1 coefficient-field recognition.
-/

public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open InvolutionTypes InvolutionCentralizers DiagramAutomorphisms EvenBorelTorus
variable {F : Type*} [Field F] [CharP F 2]

/-- Two complementary orthogonal planes in the actual natural symplectic space. -/
structure OrthogonalTwoDecomposition (F : Type*) [Field F] where
  left : Submodule F (Vector F)
  right : Submodule F (Vector F)
  isCompl : IsCompl left right
  finrank_left : Module.finrank F left = 2
  finrank_right : Module.finrank F right = 2
  orthogonal : ∀ x ∈ left, ∀ y ∈ right, form F x y = 0

namespace OrthogonalTwoDecomposition
variable (D : OrthogonalTwoDecomposition F)

/-- Each of the two summands is invariant. -/
def Fixes (g : Sp F) : Prop :=
  (∀ x ∈ D.left, g • x ∈ D.left) ∧ (∀ x ∈ D.right, g • x ∈ D.right)

/-- The two summands are interchanged. -/
def Swaps (g : Sp F) : Prop :=
  (∀ x ∈ D.left, g • x ∈ D.right) ∧ (∀ x ∈ D.right, g • x ∈ D.left)

/-- The unordered pair of summands is invariant. -/
def Permutes (g : Sp F) : Prop := D.Fixes g ∨ D.Swaps g

omit [CharP F 2] in
/-- Construct or eliminate the unordered-plane action using literal subspace inclusions. -/
theorem permutes_iff (g : Sp F) : D.Permutes g ↔
    ((∀ x ∈ D.left, g • x ∈ D.left) ∧ (∀ x ∈ D.right, g • x ∈ D.right)) ∨
      ((∀ x ∈ D.left, g • x ∈ D.right) ∧ (∀ x ∈ D.right, g • x ∈ D.left)) :=
  Iff.rfl

private theorem form_symm (x y : Vector F) : form F x y = form F y x := by
  simpa only [CharTwo.neg_eq] using TwoLocalCover.form_alternating.neg_eq x y

theorem swap_pairing (g : Sp F) (hg : g^2=1) (hs : D.Swaps g)
    (x : Vector F) : form F x (g • x) = 0 := by
  obtain ⟨u,w,hw,_⟩ := Submodule.existsUnique_add_of_isCompl D.isCompl x
  have hg2 (y : Vector F) : g • (g • y) = y := by rw [←mul_smul,←pow_two,hg,one_smul]
  have hcross : form F (w : Vector F) (g • (u : Vector F)) =
      form F (u : Vector F) (g • (w : Vector F)) := by
    rw [←preserves_form g, hg2,form_symm]
  rw [←hw,smul_add]
  simp only [map_add,LinearMap.add_apply]
  rw [
    D.orthogonal u u.property (g • (u : Vector F)) (hs.1 u u.property),
    form_symm (w : Vector F) (g • (w : Vector F)),
    D.orthogonal (g • (w : Vector F)) (hs.2 w w.property) w w.property,
    hcross]
  simp [CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem not_swaps_of_isB1 (g : Sp F) (hg : IsB1 g) : ¬ D.Swaps g := by
  intro hs
  have hb := LinearEquiv.finrank_le_displacement_of_disjoint_image (toLinear g)
    D.left D.right D.isCompl.disjoint hs.1
  change Module.finrank F D.left ≤ Module.finrank F (movedSpace g) at hb
  rw [D.finrank_left,hg.2] at hb
  omega

omit [CharP F 2] in
theorem not_commute_isB1_of_swap (g t : Sp F) (hs : D.Swaps g)
    (ht : IsB1 t) (hp : D.Permutes t) : ¬ Commute t g := by
  intro hc
  obtain ⟨hU,hW⟩ := hp.resolve_right (D.not_swaps_of_isB1 t ht)
  have he := LinearEquiv.eq_one_of_rank_one_commute_swap (toLinear t) (toLinear g)
    D.left D.right D.isCompl ht.2.le hU hW hs.1 hs.2 (by
      intro x
      change t • (g • x) = g • (t • x)
      rw [←mul_smul,←mul_smul,hc.eq])
  have hr : Module.finrank F (movedSpace t) = 0 := by
    unfold movedSpace
    rw [he]
    change Module.finrank F (LinearMap.range
      (LinearMap.id - LinearMap.id : Vector F →ₗ[F] Vector F))=0
    rw [sub_self,LinearMap.range_zero]
    exact finrank_bot F (Vector F)
  have := ht.2
  omega

end OrthogonalTwoDecomposition

/-- Every nonidentity element with alternating image pairing commutes with
a rank-one involution in the same subgroup. -/
def HasRankOneCompanions (V : Subgroup (Sp F)) : Prop :=
  ∀ g ∈ V, g ≠ 1 → (∀ x : Vector F, form F x (g • x)=0) →
    ∃ t ∈ V, IsB1 t ∧ Commute t g

theorem companion_subgroup_fixes_decomposition
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hc : HasRankOneCompanions V) (D : OrthogonalTwoDecomposition F)
    (hperm : ∀ g ∈ V, D.Permutes g) :
    ∀ g ∈ V, D.Fixes g := by
  intro g hg
  apply (hperm g hg).resolve_right
  intro hs
  by_cases hg1 : g=1
  · subst g
    have hle : D.left ≤ D.right := by intro x hx; simpa using hs.1 x hx
    have he : D.left=⊥ := by
      apply le_bot_iff.mp
      intro x hx
      exact Submodule.disjoint_def.mp D.isCompl.disjoint x hx (hle hx)
    have hd := D.finrank_left
    rw [he] at hd
    simp at hd
  · have hg2 : g^2=1 := elemPow_eq_one_of_isElementaryAbelian g hg
    obtain ⟨t,ht,htb,htc⟩ := hc g hg hg1 (D.swap_pairing g hg2 hs)
    exact D.not_commute_isB1_of_swap g t hs htb (hperm t ht) htc

omit [CharP F 2] in
theorem hasRankOneCompanions_conjugate (V : Subgroup (Sp F))
    (hc : HasRankOneCompanions V) (a : Sp F) :
    HasRankOneCompanions (V.map (MulAut.conj a).toMonoidHom) := by
  rintro y ⟨g,hg,rfl⟩ hy horth
  have hg1 : g ≠ 1 := by
    intro he
    apply hy
    simp [he]
  have hgorth (x : Vector F) : form F x (g • x)=0 := by
    have hh := horth (a • x)
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_smul,
      inv_smul_smul,preserves_form] using hh
  obtain ⟨t,ht,htb,htc⟩ := hc g hg hg1 hgorth
  refine ⟨(MulAut.conj a) t,mem_map_of_mem _ ht,?_,htc.map (MulAut.conj a).toMonoidHom⟩
  exact (isB1_conj_iff a t).mpr htb

theorem hasRankOneCompanions_of_moving_actor [Finite F] (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hV : V.map a.val.toMonoidHom = V)
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range) :
    HasRankOneCompanions V := by
  obtain ⟨σ,c,d,hc0,_hd0,hcoord⟩ := moving_actor_coordinates hq a ha
  intro g hg hg1 horth
  obtain ⟨⟨s,t⟩,he⟩ := hc hg
  have he' : upper s.toAdd t.toAdd=g := by
    simpa only [CentralRootGeometry.parameter_apply,upper] using he
  have hs : s.toAdd=0 := by
    have hh := horth (Pi.single (.inr 0) 1)
    rw [←he',upper_apply] at hh
    simpa [form_apply,Pi.single_apply,Fin.sum_univ_two,CharTwo.neg_eq] using hh
  have ht0 : t.toAdd ≠ 0 := by
    intro ht
    apply hg1
    rw [←he',hs,ht]
    simp [upper,RootSubgroup.element_zero]
  have ht : a.val g ∈ V := hV.le (mem_map_of_mem a.val.toMonoidHom hg)
  refine ⟨a.val g,ht,?_,?_⟩
  · rw [←he',hs,hcoord,map_zero,mul_zero]
    have heq : upper (c*(σ t.toAdd)^2) 0 = rootElement 0 (c*(σ t.toAdd)^2) := by
      simp [upper,RootSubgroup.element_zero]
    rw [heq]
    exact root0_isB1 (mul_ne_zero hc0 (pow_ne_zero _ ((map_ne_zero σ).mpr ht0)))
  · exact (Commute.all (⟨a.val g,ht⟩ : V) ⟨g,hg⟩).map V.subtype

/-- Any irreducible pair generated by a companion subgroup and one conjugate
excludes the orthogonal two-plane decomposition. This also applies after a
diagram twist changes the original opposition matrix. -/
theorem conjugatePair_not_permute_orthogonal_two
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hc : HasRankOneCompanions V) (a : Sp F)
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp
      (V ⊔ V.map (MulAut.conj a).toMonoidHom).subtype))
    (D : OrthogonalTwoDecomposition F) :
    ¬ (∀ g ∈ (V ⊔ V.map (MulAut.conj a).toMonoidHom), D.Permutes g) := by
  intro hp
  have hf := companion_subgroup_fixes_decomposition V hc D
    (fun g hg => hp g ((show V ≤ (V ⊔ V.map (MulAut.conj a).toMonoidHom) from le_sup_left) hg))
  let W := V.map (MulAut.conj a).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hw := companion_subgroup_fixes_decomposition W
    (hasRankOneCompanions_conjugate V hc a) D
    (fun g hg => hp g ((show W ≤ (V ⊔ V.map (MulAut.conj a).toMonoidHom) from le_sup_right) hg))
  have hI : (V ⊔ V.map (MulAut.conj a).toMonoidHom) ≤ stabilizer D.left := sup_le
    (fun g hg => (mem_stabilizer_iff _ _).mpr (hf g hg).1)
    (fun g hg => (mem_stabilizer_iff _ _).mpr (hw g hg).1)
  let U : Subrepresentation ((Representation.symplecticNatural 2).comp
    (V ⊔ V.map (MulAut.conj a).toMonoidHom).subtype) := ⟨D.left,fun g x hx =>
    (mem_stabilizer_iff _ _).mp (hI g.property) x hx⟩
  let := hi
  rcases eq_bot_or_eq_top U with hu | hu
  · have he : D.left=⊥ := congrArg Subrepresentation.toSubmodule hu
    have hd := D.finrank_left
    rw [he] at hd
    simp at hd
  · have he : D.left=⊤ := congrArg Subrepresentation.toSubmodule hu
    have hd := D.finrank_left
    rw [he] at hd
    simp [Vector] at hd


/-- The original opposition pair is a literal instance of the conjugate-pair exclusion. -/
theorem oppositePair_not_permute_orthogonal_two
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hc : HasRankOneCompanions V) (hi : Representation.IsIrreducible (pairAction V))
    (D : OrthogonalTwoDecomposition F) :
    ¬ (∀ g ∈ oppositePair V, D.Permutes g) :=
  conjugatePair_not_permute_orthogonal_two V hc opposition hi D

theorem moving_pair_not_permute_orthogonal_two [Finite F]
    (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hV : V.map a.val.toMonoidHom = V)
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hr : 2 < Nat.card V) (D : OrthogonalTwoDecomposition F) :
    ¬ (∀ g ∈ oppositePair V, D.Permutes g) :=
  oppositePair_not_permute_orthogonal_two V
    (hasRankOneCompanions_of_moving_actor hq a ha V hV
      (CentralRootGeometry.parameter_range (F := F) ▸ hc))
    (pairAction_irreducible_of_moving_actor hq a ha V hV hc hr) D

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
