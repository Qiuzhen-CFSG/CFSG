module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source

/-!
# Source context for local incidence in MS93 (1.7)

`LocalFacts` lists exactly the local-structure inputs whose construction has
an independent owner. The fixed preimage and all local centralizers retain
the definitions in `RankOnePairing.Source`. Natural coordinates show that Z
has no global fixed point, and relative normality controls the seed.

Source: Meierfrankenfeld--Stellmacher (1993), notation pp.828--829,832 and
(1.7), pp.847--848. This module does not assert either conclusion of (1.7).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M]

structure LocalFacts (e : Extension (M := M)) (Z : Subgroup M) : Prop where
  core_le : ∀ j, extensionCore e.projection ≤ localParabolic e j
  core_eq : ∀ j, localCore (localParabolic e j) = selectedCore e j
  parabolic_image : ∀ j, (localParabolic e j).map e.projection = modelParabolic e.flag j
  residual_image : ∀ j,
    (localResidual (localParabolic e j)).map e.projection = modelParabolic e.flag j
  core_image : ∀ j, (localCore (localParabolic e j)).map e.projection =
    (pCore 2 (modelParabolic e.flag j)).map (modelParabolic e.flag j).subtype
  generation : localParabolic e false ⊔ localParabolic e true = ⊤
  component_normal : (component e.projection e.flag).Normal
  component_image : (component e.projection e.flag).map e.projection = ⊤
  z_central : Z ≤ centralizer (extensionCore e.projection : Set M)
  z_irreducible : ∀ D : Subgroup M, D ≤ Z →
    component e.projection e.flag ≤ normalizer (D : Set M) → D = ⊥ ∨ D = Z

def localFixed (e : Extension (M := M)) (Z : Subgroup M) (j : Bool) : Subgroup M :=
  Z ⊓ centralizer (localCore (localParabolic e j) : Set M)

theorem fixedPreimage_commutator (L X Z : Subgroup M) [Z.Normal] :
    ⁅fixedPreimage L X Z, L⁆ ≤ Z := by
  rw [commutator_comm]
  exact commutator_le.mpr fun l hl c hc => (mem_fixedPreimage L X Z c).mp hc |>.2 l hl

theorem fixedPreimage_ambient_normal (L X Z : Subgroup M) [Z.Normal] [L.Normal] :
    (fixedPreimage L X Z).Normal := by
  let q := QuotientGroup.mk' Z
  let : (L.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective Z)
  exact inferInstanceAs (generated X ⊓ (centralizer (L.map q : Set (M ⧸ Z))).comap q).Normal

private theorem binary_fixed_zero (v : Fin 3 → ZMod 2)
    (h : ∀ g : SL, g.val.mulVec v = v) : v = 0 := by
  have h1 := h ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
  have h2 := h ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩
  have h3 := h ⟨!![1,0,0;0,1,0;1,0,1], by decide⟩
  have calc_fixed : ∀ a : Fin 3 → ZMod 2,
      (!![1,1,0;0,1,0;0,0,1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a →
      (!![1,0,0;0,1,1;0,0,1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a →
      (!![1,0,0;0,1,0;1,0,1] : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a → a = 0 := by
    decide +kernel
  exact calc_fixed v h1 h2 h3

theorem natural_fixed_eq_bot {π : M →* SL} {L Z : Subgroup M}
    (n : NaturalFactor π L Z ⊥) (hL : L.map π = ⊤) :
    Z ⊓ centralizer (L : Set M) = ⊥ := by
  apply bot_unique
  intro z hz
  have hcoord : Multiplicative.toAdd (n.coordinates ⟨z, hz.1⟩) = 0 := by
    apply binary_fixed_zero
    intro g
    have hg : n.marking.symm g ∈ L.map π := hL.symm ▸ mem_top _
    obtain ⟨l, hl, he⟩ := hg
    have hconj : z = l * z * l⁻¹ := by rw [hz.2 l hl, mul_inv_cancel_right]
    have hact := n.action l hl ⟨z, hz.1⟩ ⟨z, hz.1⟩ hconj
    rw [he, n.marking.apply_symm_apply] at hact
    exact hact.symm
  have he : n.coordinates ⟨z, hz.1⟩ = 1 := hcoord
  have hk : (⟨z, hz.1⟩ : Z) ∈ n.coordinates.ker := he
  rw [n.kernel] at hk
  exact hk

namespace LocalFacts
variable [Finite M] {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
  [Z.Normal] [W.Normal] (d : SourceData e i Z W X) (f : LocalFacts e Z)

include d in
theorem generated_le_core : generated X ≤ extensionCore e.projection :=
  generated_le X _ d.x_le

include d f in
theorem z_central_generated : Z ≤ centralizer (generated X : Set M) :=
  f.z_central.trans (centralizer_le (generated_le X _ d.x_le))

include d f in
theorem z_central_W : Z ≤ centralizer (W : Set M) :=
  f.z_central.trans (centralizer_le d.w_le)

include d f in
theorem seed_normalized : localParabolic e i ≤ normalizer (X : Set M) :=
  (normal_subgroupOf_iff_le_normalizer (d.x_le.trans (f.core_le i))).mp d.x_normal

include f in
omit [Finite M] [Z.Normal] in
theorem local_generation : localParabolic e i ⊔ localParabolic e (!i) = ⊤ := by
  cases i
  · exact f.generation
  · simpa only [Bool.not_true, sup_comm] using f.generation

end LocalFacts
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
