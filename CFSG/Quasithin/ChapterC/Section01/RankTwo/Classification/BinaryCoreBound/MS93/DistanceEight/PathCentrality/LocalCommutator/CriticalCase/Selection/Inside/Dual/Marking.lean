module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual.Action

/-!
# Marking the actual natural submodule

Transport the source model to U_c by amalgam conjugation. Equal projection
kernels give a compatible automorphism of SL3(2). Since U_c intersects D_c
trivially and Z_cD_c = U_cD_c, the literal quotient map identifies U_c with
the natural subrepresentation of <x>Z_cD_c/D_c. Its conjugation equation
proves equivariance, including the marking of the given projection.

Adapted from Reduction/Escape/EdgeTransfer/Extension/Marking.
Source: MS93 (1993), (1.5)(i), printed p.843, used in (4.4.1)(2), p.891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Dual

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
    (c : Vertex R) (ha : color R c = false)
    (π : stabilizer R c →* SL) (hπ : Function.Surjective π)
    (hker : π.ker = (Q R c).subgroupOf (stabilizer R c)) :
    ∃ (marking : SL ≃* SL) (eU : U R c ≃* Multiplicative (Fin 3 → ZMod 2)),
      ∀ (s : stabilizer R c) (u v : U R c),
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

omit [Finite M] in
private theorem natural_disjoint_fixedCore (modules : ModuleFacts source geometry)
    (c : Vertex R) (ha : color R c = false) : Disjoint (U R c) (fixedCore R c) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  exact (Escape.EdgeTransfer.U_fixed_eq_bot modules c ha).le ⟨hx.1, hx.2.2⟩

/-- The fixed summand of Z_c disappears modulo D_c. -/
private theorem Z_sup_fixedCore_eq (modules : ModuleFacts source geometry)
    (c : Vertex R) (hc : color R c = false) :
    Z R c ⊔ fixedCore R c = U R c ⊔ fixedCore R c := by
  let data : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z,modules.natural,modules.decomposition,modules.disjoint⟩
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [data.decomposition_at c hc]
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    exact le_inf (inf_le_left.trans (by
      rw [← modules.X_eq_Z c hc]; exact omegaCenter_le _))
      (inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer c)))
  · exact sup_le_sup_right (U_le_Z R c) _

private theorem natural_marking (modules : ModuleFacts source geometry)
    (c : Vertex R) (point : FreeAmalgam R) (ha : color R c = false) (A : Action c point) :
    A.HasNaturalMarking := by
  let := A.normal
  let := A.elementary
  obtain ⟨marking, eU, heU⟩ := local_natural modules c ha
    A.projection A.projection_surjective A.projection_kernel
  let H := carrier c point
  let D := (fixedCore R c).subgroupOf H
  let q := QuotientGroup.mk' D
  have hZ : Z R c ≤ H := (show Z R c ≤ layer c point from le_sup_right).trans le_sup_left
  have hU : U R c ≤ H := (U_le_Z R c).trans hZ
  have hD : fixedCore R c ≤ H := le_sup_right
  have hkill : ((fixedCore R c).subgroupOf H).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (QuotientGroup.ker_mk' D).ge
  have hImage : ((Z R c).subgroupOf H).map q = ((U R c).subgroupOf H).map q := by
    have h := congrArg (fun K : Subgroup (FreeAmalgam R) => (K.subgroupOf H).map q)
      (Z_sup_fixedCore_eq modules c ha)
    simpa only [subgroupOf_sup hZ hD, subgroupOf_sup hU hD, Subgroup.map_sup,
      hkill, sup_bot_eq] using h
  let f : U R c →* H ⧸ D := q.comp (inclusion hU)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro u hu
    have huD : (u : FreeAmalgam R) ∈ fixedCore R c :=
      (QuotientGroup.eq_one_iff (inclusion hU u)).mp hu
    exact Subtype.ext (disjoint_iff_inf_le.mp (natural_disjoint_fixedCore modules c ha)
      ⟨u.property, huD⟩)
  let F₀ := (f.comp eU.symm.toMonoidHom).toAdditiveRight.toZModLinearMap 2
  have hF₀ (v : Fin 3 → ZMod 2) : F₀ v ∈ A.natural.toSubmodule := by
    change q (inclusion hU (eU.symm (Multiplicative.ofAdd v))) ∈
      ((Z R c).subgroupOf H).map q
    exact mem_map_of_mem q (U_le_Z R c (eU.symm (Multiplicative.ofAdd v)).property)
  let F : (Fin 3 → ZMod 2) →ₗ[ZMod 2] A.natural.toSubmodule := F₀.codRestrict _ hF₀
  have hFinj : Function.Injective F := by
    intro v w h
    have hh := congrArg (fun z : A.natural.toSubmodule => z.val.toMul) h
    exact congrArg Multiplicative.toAdd (eU.symm.injective (hf hh))
  have hFsurj : Function.Surjective F := by
    intro v
    have hv : v.val.toMul ∈ ((U R c).subgroupOf H).map q := by
      rw [← hImage]
      exact v.property
    obtain ⟨u, hu, huv⟩ := hv
    let uU : U R c := ⟨u.val, hu⟩
    refine ⟨(eU uU).toAdd, Subtype.ext ?_⟩
    change Additive.ofMul (f (eU.symm (eU uU))) = v.val
    rw [eU.symm_apply_apply]
    exact congrArg Additive.ofMul huv
  let E := LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩
  refine ⟨marking, E.symm, ?_⟩
  intro g v
  obtain ⟨s, rfl⟩ := A.projection_surjective g
  obtain ⟨w, rfl⟩ := E.surjective v
  apply E.injective
  rw [E.apply_symm_apply, E.symm_apply_apply]
  let u := eU.symm (Multiplicative.ofAdd w)
  let z := Offenders.conjugation (stabilizer R c) (U R c) (U_normalized c) s u
  have hz : (z : FreeAmalgam R) =
      (s : FreeAmalgam R) * (u : FreeAmalgam R) * (s : FreeAmalgam R)⁻¹ := rfl
  have hcoords : (eU z).toAdd = (marking (A.projection s)).val.mulVec w := by
    simpa only [u, eU.apply_symm_apply, toAdd_ofAdd] using heU s u z hz
  apply Subtype.ext
  change Additive.ofMul (A.action (A.projection s) (f u)) =
    Additive.ofMul (f (eU.symm (Multiplicative.ofAdd
      ((marking (A.projection s)).val.mulVec w))))
  rw [← hcoords, ofAdd_toAdd, eU.symm_apply_apply]
  exact congrArg Additive.ofMul (A.conjugation s (inclusion hU u) (inclusion hU z) hz)

/-- The natural marking is constructed from the source model and the literal
quotient map on U_c; it is equivariant for this action's own projection. -/
theorem action_hasNaturalMarking (modules : ModuleFacts source geometry)
    (c : Vertex R) (point : FreeAmalgam R) (hc : color R c = false)
    (A : Action c point) : A.HasNaturalMarking := natural_marking modules c point hc A

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Dual
