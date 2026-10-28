module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalKernelDisplacement

/-!
# The literal critical hyperplane centralizer

A bijective natural marking identifies the critical hyperplane with
Z_z intersect Q_a. Its full pointwise fixer is the original critical root,
so the centralizer inside a marked actor is exactly Z_a joined with its
literal endpoint kernel. The endpoint then normalizes the neighboring
centralizer kernel joined with Z_a. No central extension is discarded.

Source: MS93 (3.3)(ii) and (5.7), printed pp.867 and919. The original tensor
application is GenerationTwoSymplecticKernelNormalization.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open RootHyperplaneComparison TwoLocalCover
variable {M F : Type*} [Group M] [Field F] [Finite F] [CharP F 2]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

/-- The original hyperplane fixer is precisely the critical root modulo the literal kernel. -/
theorem critical_root_hyperplane_centralizer
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hZU : Z R z = U R z)
    (Y : Subgroup (FreeAmalgam R))
    (hZY : Z R a ≤ Y) (hYZ : Y ≤ stabilizer R z)
    (f : Y →* Sp F) (hf : f.ker = (Q R z).subgroupOf Y)
    (hroot : ∀ u : Y, u.val ∈ Z R a → Module.finrank F (InvolutionTypes.movedSpace (f u)) ≤ 1)
    (π : U R z ≃* Multiplicative (Theory.SpecificGroups.SymplecticFour.Vector F))
    (hact : ∀ (y : Y) (u : U R z),
      π ⟨y.val*u.val*y.val⁻¹,
        (mem_normalizer_iff.mp (U_normalized z (hYZ y.property)) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (f y • (π u).toAdd))
    (hindex : (Q R z).relIndex (Z R a) = Nat.card F) :
    Y ⊓ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _) =
      Z R a ⊔ (Y ⊓ Q R z) := by
  let j := (U R z).subtype.comp π.symm.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp π.symm.injective
  have hjr : j.range = Z R z := by
    rw [MonoidHom.range_comp,π.symm.toMonoidHom.range_eq_top_of_surjective π.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype,←hZU]
  have hconj (y : Y) v : j (Multiplicative.ofAdd (f y • v)) =
      y.val*j (Multiplicative.ofAdd v)*y.val⁻¹ := by
    have hh := hact y (π.symm (Multiplicative.ofAdd v))
    rw [π.apply_symm_apply,toAdd_ofAdd] at hh
    have hh' := congrArg π.symm hh
    rw [π.symm_apply_apply] at hh'
    exact congrArg Subtype.val hh'.symm
  let g := f.comp (inclusion hZY)
  let := geometry.Z_elementary hb a path.start_color
  let : IsElementaryAbelian 2 g.range := IsElementaryAbelian.of_surjective g.rangeRestrict
    g.rangeRestrict_surjective
  have hgne : g.range ≠ ⊥ := by
    intro h
    apply path.critical.2
    intro x hx
    have hg : g ⟨x,hx⟩ = 1 := mem_bot.mp (h ▸ (show g ⟨x,hx⟩ ∈ g.range from ⟨_,rfl⟩))
    have hk : inclusion hZY ⟨x,hx⟩ ∈ f.ker := hg
    rw [hf] at hk
    exact hk
  obtain ⟨_,_,_,hd⟩ := elementary_transvection_common_line g.range hgne
    (by rintro x ⟨x,rfl⟩; exact hroot (inclusion hZY x) x.property)
  have hgker : g.ker = (Q R z).subgroupOf (Z R a) := by
    ext x
    change f (inclusion hZY x) = 1 ↔ x.val ∈ Q R z
    change inclusion hZY x ∈ f.ker ↔ _
    rw [hf]
    rfl
  have hgcard : Nat.card g.range = Nat.card F := by
    rw [←index_ker,hgker]
    exact hindex
  have hza := path.endpoint_Z_le_start_stabilizer hb
  have hA : ∀ v, j (Multiplicative.ofAdd v) ∈ Z R z ⊓ Q R a ↔
      v ∈ fixedSpace g.range := by
    intro v
    constructor
    · intro hv x hx
      obtain ⟨x,rfl⟩ := hx
      apply Multiplicative.ofAdd.injective
      apply hj
      change j (Multiplicative.ofAdd (f (inclusion hZY x) • v)) = _
      rw [hconj]
      have hh := (show j (Multiplicative.ofAdd v) ∈ C R a from hCa.symm ▸ hv.2).2 x.val x.property
      change x.val * j (Multiplicative.ofAdd v) * x.val⁻¹ = _
      rw [hh,mul_inv_cancel_right]
    · intro hv
      have hz : j (Multiplicative.ofAdd v) ∈ Z R z := hjr ▸ (show j (Multiplicative.ofAdd v) ∈ j.range from ⟨_,rfl⟩)
      refine ⟨hz,?_⟩
      rw [←hCa]
      refine ⟨hza hz,?_⟩
      intro x hx
      have hh := hconj (inclusion hZY ⟨x,hx⟩) v
      change j (Multiplicative.ofAdd (g ⟨x,hx⟩ • v)) = _ at hh
      rw [hv (g ⟨x,hx⟩) ⟨⟨x,hx⟩,rfl⟩] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  apply le_antisymm
  · rintro y ⟨hy,hc⟩
    have hfix : f ⟨y,hy⟩ ∈ fixingSubgroup (Sp F) (fixedSpace g.range : Set (Vector F)) := by
      apply (mem_fixingSubgroup_iff _).mpr
      intro v hv
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hconj]
      rw [←hc _ ((hA v).mpr hv),mul_inv_cancel_right]
    rw [root_fixedSpace_fixer_eq g.range hd hgcard] at hfix
    obtain ⟨x,hx⟩ := hfix
    let k : Y := (inclusion hZY x)⁻¹ * ⟨y,hy⟩
    have hk : k.val ∈ Q R z := by
      have hk' : k ∈ f.ker := by
        change f k = 1
        rw [map_mul,map_inv]
        change (g x)⁻¹ * f ⟨y,hy⟩ = 1
        rw [hx,inv_mul_cancel]
      rw [hf] at hk'
      exact hk'
    have hm := (Z R a ⊔ (Y ⊓ Q R z)).mul_mem (mem_sup_left x.property)
      (mem_sup_right ⟨k.property,hk⟩)
    change x.val * (x.val⁻¹ * y) ∈ _ at hm
    simpa only [mul_inv_cancel_left] using hm
  · apply sup_le
    · exact le_inf hZY
        ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)).trans
          (centralizer_le inf_le_right))
    · exact le_inf inf_le_left (inf_le_right.trans
        ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (geometry.centralizes z path.end_color))).trans (centralizer_le inf_le_left)))

/-- The endpoint normalizes the selected centralizer kernel joined to the
starting seed, once the literal hyperplane centralizer has been identified. -/
theorem endpoint_normalizes_neighbor_centralizer [Finite M]
    (path : CriticalPath R geometry a z) (hb : 2 < geometry.b R)
    {d t : Vertex R} (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hcent : (Z R d ⊔ Z R a) ⊓ centralizer
      ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _) =
        Z R a ⊔ ((Z R d ⊔ Z R a) ⊓ Q R z)) :
    Z R z ≤ normalizer (((Z R d ⊓ centralizer
      ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a :
        Subgroup (FreeAmalgam R)) : Set _) := by
  let Y := Z R d ⊔ Z R a
  let H := (Z R d ⊓ centralizer ((Z R z ⊓ Q R a :
    Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a
  have hYQ : Y ≤ Q R a :=
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt).trans
      (geometry.V_le_Q hb a path.start_color)
  have hHQ : H ≤ Z R a ⊔ (Y ⊓ Q R z) := by
    apply sup_le _ le_sup_left
    exact (inf_le_inf le_sup_left le_rfl).trans_eq hcent
  have hn : Q R a ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)
  have hc : ⁅Y ⊓ Q R z,Z R z⁆ = ⊥ := by
    rw [commutator_comm]
    exact le_bot_iff.mp ((commutator_mono le_rfl inf_le_right).trans
      (geometry.centralizes z path.end_color).le)
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono hHQ le_rfl).trans
    (commutator_sup_le_of_relative_normal (Q R a) (Z R a) (Y ⊓ Q R z)
      (Z R z) (Z R a) hn (le_sup_right.trans hYQ) (inf_le_left.trans hYQ)
      (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path)
      (hc ▸ bot_le))).trans le_sup_right
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
