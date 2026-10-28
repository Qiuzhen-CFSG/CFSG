module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.FullNaturalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverLarge
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.MaximizingPlane
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.GroupTheory.PCoreImageRestriction

/-!
# The maximizing parabolic at every original nonbinary degree

Choose a maximum small mover in a containing symplectic Sylow and move its
fixed plane to the standard plane. The whole edge image stays unipotent.
The natural quadratic bound controls every competing plane intersection;
the exact quotient map lifts this maximum with the entire Q-kernel.
Quadratic lifting on the same marking gives [U,Q1,Q1] = 1 on the full
original U-layer. Thus the two choices in MS93 (5.0), printed p.912, hold
simultaneously on the minimum characteristic replacement.

The later generation and fixed-layer clauses of (5.5)--(5.6), and their
selected-path and terminal-exclusion consumers, remain separate proofs.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Source (5.0)'s quadratic and maximizing choices in one literal vertex
marking. The full preimages, rather than central complements, are compared. -/
theorem Input.replacement_maximizing_parabolic
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        (let P := (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype
         let Q₁ := P.comap f
         let J := (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
           (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
         (planeParabolic.comap f).pCoreIn 2 = Q₁ ∧
         (Q d.radical t).subgroupOf (stabilizer d.radical a) ≤ planeParabolic.comap f ∧
         ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),Q₁⁆,Q₁⁆ = ⊥ ∧
           ∀ x : Sp E.Carrier,
             Nat.card (J ⊓ (P.map (MulAut.conj x).toMonoidHom).comap f :
               Subgroup (stabilizer d.radical a)) ≤ Nat.card (J ⊓ Q₁ :
                 Subgroup (stabilizer d.radical a))) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hglobal,hidx,hquad⟩ :=
    h.replacement_small_mover_quadratic_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier^2)
  have hJmap : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hfQ,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS,hcard]
  have hJsub : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf S = J := by
    rw [←hJmap]
    exact comap_map_eq_self_of_injective S.subtype_injective _
  have hTi : T.map f ≤ unipotent.subtype.range := by simpa only [range_subtype] using hTf
  have hcoord := Degree.Quotient.coordinates_join U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx
  have hJTi : J.map f ≤ unipotent.subtype.range :=
    (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hTi
  have hJcoord := Degree.Quotient.coordinates_map f unipotent.subtype J hJTi
  have hlarge : Nat.card E.Carrier^2 ≤
      Nat.card (Degree.join (Degree.Quotient.coordinates f unipotent.subtype T)) := by
    have hc : Nat.card (Degree.join (Degree.Quotient.coordinates f unipotent.subtype T)) =
        f.ker.relIndex J := by
      rw [←hcoord,relIndex_ker,←hJcoord,card_map_of_injective Subtype.val_injective]
    rw [hc]
    have he := relIndex_map_map_of_injective f.ker J S.subtype_injective
    rw [hfQ,hJmap] at he
    rw [←he,hcard]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  obtain ⟨g,hTg,hmax⟩ := Degree.exists_maximizing_plane _ hlarge
  have hTcoord := Degree.Quotient.coordinates_map f unipotent.subtype T hTi
  rw [hTcoord] at hTg
  rw [←hcoord,hJcoord] at hmax
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf' : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact hTg
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x)=1 ↔ f x=1
    exact (MulAut.conj g).map_eq_one_iff
  have hkJ : f'.ker ≤ J := by
    rw [hker]
    exact Subgroup.SmallMover.kernel_le_join U₀ f.ker T _
      (Nat.one_le_pow _ _ Nat.card_pos) hkT hUK
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,
    hTf',?_,?_⟩
  · intro A
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hglobal A
  · dsimp only
    rw [hJsub]
    let P := (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype
    let Q₁ := P.comap f'
    have hQquad : IsQuadratic (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.Carrier) 2)) (Q₁.map f') := by
      rintro x hx y hy v
      exact Degree.plane_radical_quadratic x (map_comap_le _ _ hx)
        y (map_comap_le _ _ hy) v
    have hpker : IsPGroup 2 f'.ker := by
      rw [hker,hQeq]
      exact (Q_isPGroup d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) a ha).comap_subtype
    have hPcore : (planeParabolic (F := E.Carrier)).pCoreIn 2 = P := by
      rw [pCoreIn,planeParabolic_core_map_eq_radical E.card_eq (by rw [hE]; exact h.nonbinary)]
      exact SymplecticConjugatePair.planeRadical_eq_wing
    have hPpre := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f'
      (planeParabolic.comap f') hpker
    rw [map_comap_eq_self_of_surjective ((MulAut.conj g).surjective.comp hf),hPcore] at hPpre
    have hQP : Q₁ ≤ planeParabolic.comap f' := by
      apply comap_mono
      rw [←hPcore]
      exact pCoreIn_le 2 _
    refine ⟨hPpre.symm.trans (inf_eq_right.mpr hQP),?_,?_,?_⟩
    · exact (map_le_iff_le_comap).mp (hTf'.trans
        (unipotent_le_borel.trans inf_le_right))
    · apply hquad Q₁
      have hh := Degree.quadratic_conjugate (Q₁.map f') g⁻¹ hQquad
      have hm : (Q₁.map f').map (MulAut.conj g⁻¹).toMonoidHom = Q₁.map f := by
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [f',MulAut.conj_apply,mul_assoc]
      rwa [hm] at hh
    · intro x
      have him (D : Subgroup (Sp E.Carrier)) :
          (J ⊓ D.comap f').map f' = J.map f' ⊓ D := by
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          exact ⟨mem_map_of_mem f' hz.1,hz.2⟩
        · rintro ⟨⟨z,hz,rfl⟩,hy⟩
          exact ⟨z,⟨hz,hy⟩,rfl⟩
      have hk (D : Subgroup (Sp E.Carrier)) : f'.ker ≤ J ⊓ D.comap f' := by
        refine le_inf hkJ ?_
        intro z hz
        change f' z ∈ D
        rw [MonoidHom.mem_ker.mp hz]
        exact D.one_mem
      have hc (D : Subgroup (Sp E.Carrier)) :
          Nat.card (J ⊓ D.comap f' : Subgroup S) =
            Nat.card (J.map f' ⊓ D : Subgroup (Sp E.Carrier)) * Nat.card f'.ker := by
        rw [←relIndex_mul_card_of_le (hk D),relIndex_ker,him]
      rw [hc,hc]
      apply Nat.mul_le_mul_right
      simpa only [f',←Subgroup.map_map] using hmax x

/-- A small-index overgroup inside the original edge cannot enlarge the
maximum-small-mover join. This is the maximality step used by (5.5). -/
theorem Input.replacement_small_mover_absorbs
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ Q d.radical t)
    (hJA : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) ≤ A)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2) :
    A = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAT) (inclusion_injective _)
  have hlarge := h.replacement_small_mover_join_index d geometry hb ha hat
  have hi := relIndex_le_of_le_right hJA (index_ne_zero_of_finite (H := (Q d.radical a).subgroupOf A))
  obtain ⟨B,hB⟩ := Subgroup.SmallMover.maximal_nonempty (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos)
  have hBJ : B ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := le_sSup hB
  have he : B = A := eq_of_le_of_card_ge (hBJ.trans hJA)
    (hB.2 A ⟨hAT,hindex.trans (hlarge.trans hi),hindex⟩)
  exact le_antisymm (he ▸ hBJ) hJA

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
