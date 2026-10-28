module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.Residual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.InvariantProjection

/-!
# Containment from the actual inner action on the star component

For a centerless normal L*, uniqueness constructs the inner projection of
Y₊* onto L*. The S₃ shadow makes Y₊ solvable, and theta generation makes
its nontrivial projection contain an element of order three. The preimage
of this solvable projection inside L is solvable: the restricted star
kernel is a proper normal subgroup of a C-component. Its invariance under
Y₊S puts it in M_I. The Sylow-residual argument then gives Y₊ ≤ L.

Only general projection and theta-image lemmas are reused from
`InvariantProjection`; no later source theorem or rank-two elimination is
used. Relative normality and the actual centerless inner action remain
explicit inputs of this helper. Their source producers are separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27(2), printed p.1131 (PDF p.1148), case (i).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement
variable {G : Type*} [Group G] [Finite G]

private theorem yplus_solvable (d : LocalData G) {I : Subgroup G}
    (h : RankOneFacts d I) : Group.IsSolvable d.Yplus := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  have hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let := hs
  obtain ⟨e⟩ := h.shadow
  let : Group.IsSolvable ((d.Yplus ⊔ d.S : Subgroup G) ⧸
      pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 (d.Yplus ⊔ d.S : Subgroup G))).mpr
      ⟨inferInstance, inferInstance⟩
  exact Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show d.Yplus ≤ d.Yplus ⊔ d.S from le_sup_left))

private theorem component_kernel_solvable
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (f : c.L →* d.Star I) (hf : f.range = d.starImage I c.L) :
    Group.IsSolvable f.ker := by
  have hk : f.ker ≠ ⊤ := by
    intro ht
    apply component_star_ne_bot d c
    rw [← hf]
    apply eq_bot_iff.mpr
    rintro _ ⟨l, rfl⟩
    exact (show l ∈ f.ker from ht ▸ mem_top l)
  let e := subgroupOfEquivOfLe c.le_thompson
  let K := f.ker.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro he
    apply hk
    apply comap_injective (f := e.toMonoidHom) e.surjective
    simpa only [comap_top] using he
  let : Group.IsSolvable K := c.component.isSolvable_of_subnormal_lt_top
    (inferInstance : K.Normal).isSubnormal hK
  have hs : Group.IsSolvable (K.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective K)
  rwa [map_comap_eq_self_of_surjective e.surjective] at hs

open FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction in
/-- The inner-action case of 15.3.27(2), after relative normality and the
centerless inner-action conclusion of the model comparison. The projection
and its invariant solvable preimage are constructed, and the needed cubic
element is obtained from theta generation. No containment is assumed. -/
theorem yplus_le_component_of_inner_star_action
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal)
    (h6 : theta (d.MI I) = d.Yplus)
    (hz : center (d.starImage I c.L) = ⊥)
    (hi : ∀ y : d.starImage I d.Yplus, ∃ l : d.starImage I c.L,
      ∀ x : d.starImage I c.L,
        (l : d.Star I) * x * l⁻¹ = y * x * y⁻¹) : d.Yplus ≤ c.L := by
  let Ls := d.starImage I c.L
  let Ys := d.starImage I d.Yplus
  let : Ls.Normal := hn.map (d.starMap I) (QuotientGroup.mk'_surjective _)
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  have hinner : ∀ y : Ys, ∃ l : Ls,
      MulAut.conj l = (MulAut.conjNormal y : MulAut Ls) := by
    intro y
    obtain ⟨l, hl⟩ := hi y
    exact ⟨l, MulEquiv.ext (fun x => Subtype.ext (hl x))⟩
  obtain ⟨π, hπ⟩ := exists_inner_projection Ls Ys hz hinner
  have hπne := inner_projection_ne_one Ls Ys (component_star_commutator d c hYI)
    (component_star_ne_bot d c) π hπ
  let j : d.Yplus →* Ys := ((d.starMap I).subgroupMap (d.Yplus.subgroupOf I)).comp
    (subgroupOfEquivOfLe hYI).symm.toMonoidHom
  have hj : Function.Surjective j := ((d.starMap I).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hYI).symm.surjective
  let r := Ls.subtype.comp (π.comp j)
  let P := r.range
  have hP : P = π.range.map Ls.subtype := by
    change (Ls.subtype.comp (π.comp j)).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ hj, ← MonoidHom.range_eq_map]
  have hPL : P ≤ Ls := hP ▸ map_subtype_le π.range
  have hPne : P ≠ ⊥ := by
    intro hb
    have hh : π.range = ⊥ := (π.range.map_eq_bot_iff_of_injective Ls.subtype_injective).mp
      (hP ▸ hb)
    apply hπne
    apply MonoidHom.ext
    intro y
    exact (show π y ∈ (⊥ : Subgroup Ls) from hh ▸ ⟨y, rfl⟩)
  have hYθ : theta d.Yplus = d.Yplus := by rw [← h6, theta_idempotent]
  obtain ⟨p, hp, hp3⟩ := exists_cubic_of_theta P (theta_range_eq_self _ hYθ r) hPne
  have hdP : 3 ∣ Nat.card P := by
    rw [← hp3, P.orderOf_coe ⟨p, hp⟩]
    exact orderOf_dvd_natCard (⟨p, hp⟩ : P)
  let : Group.IsSolvable d.Yplus := yplus_solvable d h
  let : Group.IsSolvable P := Group.isSolvable_of_surjective r.rangeRestrict_surjective
  have hYSY : d.Yplus ⊔ d.S ≤ normalizer (d.Yplus : Set G) := by
    rw [← h6]
    apply le_trans ?_ ((d.MI I).le_normalizer.trans (normalizer_le_normalizer_theta _))
    exact sup_le (theta_le _) (le_inf (inf_le_left.trans d.sylow_le)
      (le_sup_right.trans hI.1.2))
  have hNs : d.starImage I (d.Yplus ⊔ d.S) ≤ normalizer (Ys : Set (d.Star I)) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨i, hi, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨i * y * i⁻¹, (hYSY hi y).mp hy, ?_⟩
    simp only [map_mul, map_inv]
  have hPN : d.starImage I (d.Yplus ⊔ d.S) ≤ normalizer (P : Set (d.Star I)) := by
    rw [hP]
    exact inner_projection_range_normalized Ls Ys _ hz hNs π hπ
  let f := (d.starMap I).comp (inclusion (component_le c))
  have hf : f.range = Ls := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  let : Group.IsSolvable f.ker := component_kernel_solvable d c f hf
  let N := P.comap f
  let : Group.IsSolvable N := isSolvable_comap_of_solvable_ker f P
  let X := N.map c.L.subtype
  have hXL : X ≤ c.L := map_subtype_le N
  have hXN : d.Yplus ⊔ d.S ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    rintro i hi _ ⟨l, hl, rfl⟩
    have hiI := hI.1.2 hi
    have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn
    refine ⟨⟨i * l * i⁻¹, (hIL hiI l).mp l.property⟩, ?_, rfl⟩
    have hc := (hPN (mem_map.mpr ⟨⟨i, hiI⟩, hi, rfl⟩) (f l)).mp hl
    change (d.starMap I) ⟨i, hiI⟩ * (d.starMap I) ⟨l, (component_le c) l.property⟩ *
      ((d.starMap I) ⟨i, hiI⟩)⁻¹ ∈ P at hc
    change (d.starMap I) ((⟨i, hiI⟩ : I) * ⟨l, (component_le c) l.property⟩ *
      (⟨i, hiI⟩ : I)⁻¹) ∈ P
    simpa only [map_mul, map_inv] using hc
  let fN : N →* P := (f.comp N.subtype).codRestrict P (fun x => x.property)
  have hfN : Function.Surjective fN := by
    intro p
    obtain ⟨l, hl⟩ := (show (p : d.Star I) ∈ f.range from hf ▸ hPL p.property)
    exact ⟨⟨l, show f l ∈ P from hl ▸ p.property⟩, Subtype.ext hl⟩
  have hdX : 3 ∣ Nat.card X := by
    rw [card_map_of_injective c.L.subtype_injective]
    exact hdP.trans (card_dvd_of_surjective fN hfN)
  exact yplus_le_component_of_invariant_solvable d c h hcontrol hn hXL
    (Group.isSolvable_of_surjective (c.L.subtype.subgroupMap_surjective N)) hXN hdX

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement
