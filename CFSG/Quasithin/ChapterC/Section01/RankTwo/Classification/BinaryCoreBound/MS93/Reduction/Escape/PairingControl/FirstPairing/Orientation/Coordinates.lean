module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Source

/-!
# Compatible coordinates for the first pairing

Transport the given natural U by actual amalgam conjugation, and compare the
transported source quotient with any specified surjection having kernel Q.
This constructs natural coordinates on U for the same projection as the full
moving section of V/Z. An outer difference between their markings then gives
actual contragredient coordinates, with kernel Z[V,Q], by the checked
inner/graph decomposition of automorphisms of SL3(2).

The natural-transport proof is adapted from the private `local_natural` in
Escape/EdgeTransfer/Extension/Marking.lean. Its elementary argument is repeated
here to preserve that module's boundary and avoid importing the neighboring
extension construction. The coordinate change follows RankOnePairing/Duality.
No orientation exclusion or source pairing hypothesis is assumed proved here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), pp.883--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation
open RankOnePairing

private noncomputable def changeCoordinates (g : SL) :
    Multiplicative (Fin 3 → ZMod 2) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' g⁻¹).toAddEquiv

private theorem changeCoordinates_apply (g : SL) (v : Multiplicative (Fin 3 → ZMod 2)) :
    (changeCoordinates g v).toAdd = g⁻¹.val.mulVec v.toAdd := rfl

private theorem untwist (g a : SL) (v : Fin 3 → ZMod 2) :
    g⁻¹.val.mulVec ((g * a * g⁻¹).val.mulVec v) =
      a.val.mulVec (g⁻¹.val.mulVec v) := by
  have h : g⁻¹ * (g * a * g⁻¹) = a * g⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec] using
    congrArg (fun b : SL => b.val.mulVec v) h

/-- A noninner relative marking constructs coordinates with the literal
inverse-transpose action of the reference natural subgroup. -/
noncomputable def dualFactorOfNotInner {A : Type*} [Group A]
    {π : A →* SL} {K H N Z : Subgroup A}
    (z : NaturalFactor π K Z ⊥) (n : NaturalFactor π K H N)
    (h : z.marking.symm.trans n.marking ∉ MulAut.innerSubgroup SL) :
    DualFactor π K H N Z z := by
  let r := z.marking.symm.trans n.marking
  let outer := BinaryLinearThree.AutomorphismAction.outer_eq_inner_graph r h
  let g := Classical.choose outer
  have hg := Classical.choose_spec outer
  let t := changeCoordinates g
  refine {
    coordinates := t.toMonoidHom.comp n.coordinates
    surjective := t.surjective.comp n.surjective
    kernel := ?_
    normalized := n.normalized
    action := ?_ }
  · ext x
    change t (n.coordinates x) = 1 ↔ x ∈ N.subgroupOf H
    rw [← t.map_one, t.injective.eq_iff]
    exact SetLike.ext_iff.mp n.kernel x
  · intro l hl x y hy
    change (changeCoordinates g (n.coordinates y)).toAdd =
      ((z.marking (π l))⁻¹.val).transpose.mulVec
        (changeCoordinates g (n.coordinates x)).toAdd
    simp only [changeCoordinates_apply]
    rw [n.action l hl x y hy]
    have he := congrArg (fun a : MulAut SL => a (z.marking (π l))) hg
    have hm : n.marking (π l) = g *
        BinaryLinearThree.AutomorphismAction.graph (z.marking (π l)) * g⁻¹ := by
      simpa only [r, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.mul_apply, MulAut.conj_apply] using he
    rw [hm, untwist]
    rfl

private theorem compare_projections {G H : Type*} [Group G] [Group H]
    (π σ : G →* H) (hπ : Function.Surjective π) (hσ : Function.Surjective σ)
    (hker : π.ker = σ.ker) :
    ∃ e : H ≃* H, ∀ x, e (π x) = σ x := by
  let eπ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let eσ := QuotientGroup.quotientKerEquivOfSurjective σ hσ
  let e := eπ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans eσ)
  refine ⟨e, ?_⟩
  intro x
  have hπx : eπ (QuotientGroup.mk' π.ker x) = π x := rfl
  rw [← hπx]
  change eσ (QuotientGroup.quotientMulEquivOfEq hker
    (eπ.symm (eπ (QuotientGroup.mk' π.ker x)))) = σ x
  rw [eπ.symm_apply_apply]
  rfl

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem local_natural (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (π : stabilizer R a →* SL) (hπ : Function.Surjective π)
    (hker : π.ker = (Q R a).subgroupOf (stabilizer R a)) :
    ∃ (marking : SL ≃* SL) (eU : U R a ≃* Multiplicative (Fin 3 → ZMod 2)),
      ∀ (s : stabilizer R a) (u v : U R a),
        (v : FreeAmalgam R) = (s : FreeAmalgam R) * (u : FreeAmalgam R) * (s : FreeAmalgam R)⁻¹ →
        (eU v).toAdd = (marking (π s)).val.mulVec (eU u).toAdd := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl, ← map_map,
      ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  have hκ : (π.comp e.toMonoidHom).ker = source.projection.ker := by
    rw [source.projection_kernel]
    ext x
    change e x ∈ π.ker ↔ x ∈ pCore 2 M
    rw [hker, ← hQ]
    constructor
    · rintro ⟨y, hy, hexy⟩
      exact e.injective hexy ▸ hy
    · intro hx
      exact mem_map_of_mem _ hx
  obtain ⟨τ, hτ⟩ := compare_projections (π.comp e.toMonoidHom) source.projection
    (hπ.comp e.surjective) source.projection_surjective hκ
  have hu : (U R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom = U R (mVertex R g) := by
    have hh := U_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  let eU : U R (alpha R) ≃* U R (mVertex R g) :=
    ((U R (alpha R)).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).trans (MulEquiv.subgroupCongr hu)
  have heU (u : U R (mVertex R g)) :
      MulAut.conj g⁻¹ (eU.symm u : FreeAmalgam R) = (u : FreeAmalgam R) :=
    congrArg Subtype.val (eU.apply_symm_apply u)
  have heS (s : S) : MulAut.conj g⁻¹ (embedM R (e.symm s)) = (s : FreeAmalgam R) :=
    congrArg Subtype.val (e.apply_symm_apply s)
  refine ⟨τ.trans modules.natural.marking, eU.symm.trans modules.natural.equiv, ?_⟩
  intro s u v hv
  have hact := modules.natural.action (e.symm s) (eU.symm u) (eU.symm v) (by
    apply (MulAut.conj g⁻¹).injective
    simp only [map_mul (MulAut.conj g⁻¹), map_inv (MulAut.conj g⁻¹), heU, heS]
    exact hv)
  have hτs : τ (π s) = source.projection (e.symm s) := by
    simpa using hτ (e.symm s)
  simpa only [MulEquiv.trans_apply, hτs] using hact

/-- Natural coordinates on the actual subgroup U inside its vertex stabilizer,
for any genuine marking of that stabilizer modulo Q. -/
theorem naturalU_nonempty (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (π : stabilizer R a →* SL) (hπ : Function.Surjective π)
    (hker : π.ker = (Q R a).subgroupOf (stabilizer R a)) :
    Nonempty (NaturalFactor π ⊤ ((U R a).subgroupOf (stabilizer R a)) ⊥) := by
  obtain ⟨marking, eU, heU⟩ := local_natural modules a ha π hπ hker
  let e : (U R a).subgroupOf (stabilizer R a) ≃* U R a :=
    Subgroup.subgroupOfEquivOfLe ((U_le_Z a).trans (Z_le_stabilizer R a))
  let f := e.trans eU
  refine ⟨{ marking := marking
            coordinates := f.toMonoidHom
            surjective := f.surjective
            kernel := ?_
            normalized := ?_
            action := ?_ }⟩
  · rw [(MonoidHom.ker_eq_bot_iff f.toMonoidHom).mpr f.injective]
    simp
  · let := normal_subgroupOf_of_le_normalizer (U_normalized a)
    exact le_normalizer_of_normal
  · intro s _ u v hv
    exact heU s (e u) (e v) (congrArg Subtype.val hv)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation
