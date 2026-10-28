module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NormalizedCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverLarge
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalRefinement

/-!
# No refinement for the edge under an arbitrary full quotient marking

The actual edge is normalized by a full vertex Sylow. Its quotient order
is at least q², by the original small-mover join bound. Both facts survive
any surjective marking with the full Q_a kernel. Conjugating the marked
Sylow to the standard one therefore excludes an invariant refinement.

This supplies the marking-independent edge obstruction used in MS93
(5.12)(2), printed p.926. The statement retains the supplied marking and
does not require an equality of natural fixed indices between markings.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full edge image preserves no refinement in any surjective
symplectic marking with the actual full vertex kernel and field degree. -/
theorem Input.replacement_edge_no_refinement_of_marking
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E : BinaryField) (hE : E.degree = n)
    (f : stabilizer d.radical a →* Sp E.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a) :
    ¬ ∃ c : Vector E.Carrier,
      ∀ x : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f,
        ∀ v, refinement c (x.val • v) = refinement c v := by
  let V := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf V
  let := finite_stabilizer d.radical a
  have hTV : Q d.radical t ≤ V := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  let : Finite (Q d.radical t) :=
    Finite.of_injective (inclusion hTV) (inclusion_injective hTV)
  have hlarge : Nat.card F ^ 2 ≤ (Q d.radical a).relIndex (Q d.radical t) :=
    (h.replacement_small_mover_join_index d geometry hb ha hat).trans
      (relIndex_le_of_le_right (Subgroup.SmallMover.join_le _ _ _ _) index_ne_zero_of_finite)
  obtain ⟨P,hTP,hPn⟩ := h.replacement_edge_normalizing_sylow d ha hat
  let S := P.mapSurjective (f := f) hf
  have hS : T.map f ≤ (S : Subgroup _) := map_mono hTP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun S : Sylow 2 (Sp E.Carrier) => (S : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hS).trans_eq hSm
  have hTn : unipotent ≤ normalizer (T.map f' : Set (Sp E.Carrier)) := by
    have hh := (map_mono (f := f) hPn).trans (le_normalizer_map f)
    have hh' := (map_mono (f := (MulAut.conj g).toMonoidHom) hh).trans
      (le_normalizer_map (MulAut.conj g).toMonoidHom)
    change ((S : Subgroup _).map (MulAut.conj g).toMonoidHom) ≤ _ at hh'
    rw [hSm,Subgroup.map_map] at hh'
    exact hh'
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  let T₀ := (T.map f').subgroupOf unipotent
  let : T₀.Normal := normal_subgroupOf_of_le_normalizer hTn
  have hT₀ : T₀.map unipotent.subtype = T.map f' := map_subgroupOf_eq_of_le hTf
  have hcardT : Nat.card T₀ = (Q d.radical a).relIndex (Q d.radical t) := by
    rw [←card_map_of_injective unipotent.subtype_injective,hT₀,←relIndex_ker]
    have he := relIndex_map_map_of_injective f'.ker T V.subtype_injective
    rw [hker,hfQ,map_subgroupOf_eq_of_le hTV] at he
    rw [hker]
    exact he.symm
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hF : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hno := CentralRootGeometry.normal_no_refinement hF T₀
    (by rw [hcardT,hcard]; exact hlarge)
  rintro ⟨c,hc⟩
  obtain ⟨c',hc'⟩ := refinement_comp_symplectic c g⁻¹
  apply hno
  refine ⟨c',?_⟩
  intro x v
  obtain ⟨y,hy,he⟩ := x.property
  change f' y = x.val.val at he
  rw [←he,←hc',←hc']
  change refinement c (g⁻¹ • ((g*f y*g⁻¹) • v)) = refinement c (g⁻¹ • v)
  simp only [mul_smul,inv_smul_smul]
  exact hc ⟨f y,mem_map_of_mem f hy⟩ _

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
