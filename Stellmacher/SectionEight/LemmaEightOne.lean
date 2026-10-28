module

public import Stellmacher.LaterDefs
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Stellmacher.SectionEight.LemmaEightOneResidualJoin
public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.DirectProductCommutator
public import Stellmacher.QuotientModuleCommutator
public import Stellmacher.QuotientModuleFixedPoints

/-!
# Stellmacher (8.1): the noncommuting critical-pair decomposition

The conclusion compares the endpoint indices and records the decomposition
of the faithful local group acting on the original center module. The action
is given by an explicit quotient-module witness, so the module itself is not
collapsed into the centralizer kernel.

The source's J(Z_a, barred S) is Section 1's J for the witness action and the
image of S in the quotient. An earlier transcription used the ambient LocalJ,
whose raw subgroup-order denominator does not agree with the faithful image
order. The present field follows the bars in the scan, journal p.37, (8.1).
Lifts remain explicit only to interpret ambient commutators and centralizers.

The endpoint index equality and nontrivial quotient offender are imported
from their proved local modules. Apply (1.7) to the projected Sylow under
the witness's exact action. Its normal closure is the projected local
residual joined with J, by the residual-join lemma. Injective subtype maps
transport the factor modules and their product, while quotient-action
transport identifies their ambient commutators and the fixed centralizer.
Finally the opposite endpoint image lies in J: its action commutator splits
over the invariant factor modules, giving the asserted product for R.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven
open CosetGraphContext

universe u

/-- The decomposition asserted in (8.1), presented through an explicit
quotient witness for `\bar G_a = G_a/C_{G_a}(Z_a)`.  The use of `Fin r`
records that the displayed direct products are finite products. -/
public structure LemmaEightOneConclusion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : Prop where
  quotient_index:
    QuotientCardEqual
      (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a' ⊓ QAt ctx.Γ ctx.criticalPath.a)
  barred_decomposition:
    ∃ w : QuotientModuleWitness
        (GAt ctx.Γ ctx.criticalPath.a)
        (GAt ctx.Γ ctx.criticalPath.a ⊓
          Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
        (ZAt ctx.Γ ctx.criticalPath.a),
      let _ := w.groupX
      let _ := w.finiteX
      let _ := MulDistribMulAction.compHom
        (ZAt ctx.Γ ctx.criticalPath.a) w.action
      ∃ r : ℕ,
        ∃ Ebar : Fin r → Subgroup w.X,
        ∃ Elift : Fin r → Subgroup (GAt ctx.Γ ctx.criticalPath.a),
        ∃ V : Fin r → Subgroup H,
        ∃ V0 : Subgroup H,
        ∃ Jbar : Subgroup w.X,
        ∃ Jlift : Subgroup (GAt ctx.Γ ctx.criticalPath.a),
          let Zbar :=
            ZAt ctx.Γ ctx.criticalPath.a
          let EbarA :=
            ((EAt ctx.Γ ctx.criticalPath.a).subgroupOf
                (GAt ctx.Γ ctx.criticalPath.a)).map w.projection ⊔ Jbar
          let Rbar :=
            ⁅Zbar, ZAt ctx.Γ ctx.criticalPath.a'⁆
          Jbar = Jlift.map w.projection ∧
          Jbar = SectionOne.oneJ (G := w.X) (V := Zbar)
            ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ∧
          (∀ i : Fin r,
            Ebar i = (Elift i).map w.projection ∧
              V i = ⁅Zbar, (Elift i).map
                (GAt ctx.Γ ctx.criticalPath.a).subtype⁆) ∧
          EbarA = ⨆ i : Fin r, Ebar i ∧
          IsInternalDirectProductFamily EbarA Ebar ∧
          (∀ i : Fin r, IsModel (Ebar i) SL2Two) ∧
          Zbar = V0 ⊔ (⨆ i : Fin r, V i) ∧
          IsInternalDirectProductFamily Zbar
            (fun o : Option (Fin r) =>
              match o with | none => V0 | some i => V i) ∧
          V0 = Zbar ⊓ Subgroup.centralizer
            ((EAt ctx.Γ ctx.criticalPath.a ⊔
              Jlift.map (GAt ctx.Γ ctx.criticalPath.a).subtype :
                Subgroup H) : Set H) ∧
          (∀ i : Fin r, Nat.card (V i) = 4) ∧
          Rbar = ⨆ i : Fin r, (Rbar ⊓ V i) ∧
          IsInternalDirectProductFamily Rbar
            (fun i : Fin r => Rbar ⊓ V i)

/-- **Stellmacher (8.1).**  Under Hypothesis 2 and
`[Z_a,Z_{a'}] ≠ 1`, the two quotient indices are equal and the barred
`E_a J(Z_a,\bar S)` and `\bar Z_a` have the displayed direct-product
decompositions. -/
public theorem lemma_eight_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    LemmaEightOneConclusion ctx := by
  classical
  refine ⟨lemma_eight_one_index ctx, ?_⟩
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Za := z Γ cp.a
  have h74 := lemma_seven_four h Γ cp
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hzq : Za ≤ q Γ cp.a :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hqP : q Γ cp.a ≤ P := by
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  obtain ⟨w⟩ := exists_quotientModuleWitness P Za
    (hzq.trans hqP) (stabilizer_le_normalizer_z Γ cp.a)
  refine ⟨w, ?_⟩
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom Za w.action
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := Za) Sb
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hZendS : z Γ cp.a' ≤ S := by
    have hdist : Γ.distance cp.a' cp.firstStep < cp.length := by
      rw [Γ.distance_symm]
      have hd := SevenSix.path_distance_le Γ cp 1 cp.length (by omega) le_rfl
      have hd' : Γ.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
        simpa [cp.path_first, cp.path_end] using hd
      omega
    exact (SevenSix.critical_minimality Γ cp hdist).trans
      (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnotcentral : ¬ z Γ cp.a' ≤ Subgroup.centralizer (z Γ cp.a : Set H) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w (z Γ cp.a')
    (hZendS.trans hSP) hnotcentral
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨_, U, hU⟩ := hP.1.1.2.1
  have hUSP : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUSP]
  have hoff := lemma_eight_one_offender ctx w
  have hJnot : SectionOne.oneJ (V := Za) (Ub : Subgroup w.X) ≠ ⊥ := by
    rw [hUb]
    exact hoff.2
  obtain ⟨r, D, Vf, hD, hSL, hVf, hV⟩ :=
    (SectionOne.lemma_one_seven hlocal Ub hJnot).part_c
  rw [hUb] at hD hV
  have hJoin := lemma_eight_one_residual_join ctx w
  let E := SectionOne.oneE (V := Za) Sb
  let Vzero := FixedPoints.subgroup E Za
  let Dlift : Fin r → Subgroup P := fun i => (D i).comap w.projection
  let Vl : Fin r → Subgroup H := fun i => (Vf i).map Za.subtype
  let Jlift := J.comap w.projection
  have hJimage : Jlift.map w.projection = J :=
    Subgroup.map_comap_eq_self_of_surjective w.surjective J
  have hDimage (i : Fin r) : (Dlift i).map w.projection = D i :=
    Subgroup.map_comap_eq_self_of_surjective w.surjective (D i)
  have hVi (i : Fin r) : Vl i = ⁅Za, (Dlift i).map P.subtype⁆ := by
    change (Vf i).map Za.subtype = _
    rw [(hVf i).1]
    exact w.commutatorAction_map_subtype (D i)
  have hVambient : IsInternalDirectProductFamily Za
      (fun o : Option (Fin r) => match o with
        | none => Vzero.map Za.subtype | some i => Vl i) := by
    have hh := hV.map_injective Za.subtype Za.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    convert hh using 1
    funext o
    cases o <;> rfl
  have hVgen : Za = Vzero.map Za.subtype ⊔ ⨆ i, Vl i := by
    simpa only [iSup_option] using hVambient.1
  let Y := Γ.e cp.a ⊔ Jlift.map P.subtype
  have hEaP : Γ.e cp.a ≤ P := by
    have heq : Γ.e cp.a = twoResidualAmbient P := Γ.twoResidualAt_def cp.a
    rw [heq]
    exact Subgroup.map_subtype_le _
  have hYP : Y ≤ P := sup_le hEaP (Subgroup.map_subtype_le _)
  have hJsub : (Jlift.map P.subtype).subgroupOf P = Jlift :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective Jlift
  have hYimage : (Y.subgroupOf P).map w.projection = E := by
    change ((Γ.e cp.a ⊔ Jlift.map P.subtype).subgroupOf P).map w.projection = E
    rw [Subgroup.subgroupOf_sup hEaP (Subgroup.map_subtype_le _),
      Subgroup.map_sup, hJsub, hJimage]
    exact hJoin.symm
  let B := ((z Γ cp.a').subgroupOf P).map w.projection
  have hBJ : B ≤ J := le_sSup hoff.1
  have hJE : J ≤ E := Subgroup.subset_normalClosure
  have hmodule : IsInternalDirectProductFamily (⊤ : Subgroup Za)
      (fun o : Option (Fin r) => o.elim (FixedPoints.subgroup E Za)
        (fun i => commutatorAction (D i) Za)) := by
    convert hV using 1
    funext o
    cases o with
    | none => rfl
    | some i => exact (hVf i).1.symm
  have hRprod := hD.commutatorAction hmodule B (hBJ.trans hJE)
  have hRmap := w.commutatorAction_image_map_subtype (z Γ cp.a') (hZendS.trans hSP)
  dsimp only at hRmap
  have hRambient : IsInternalDirectProductFamily ⁅Za, z Γ cp.a'⁆
      (fun i => ⁅Za, z Γ cp.a'⁆ ⊓ Vl i) := by
    have hh := hRprod.map_injective Za.subtype Za.subtype_injective
    change IsInternalDirectProductFamily ((commutatorAction B Za).map Za.subtype)
      (fun i => (commutatorAction B Za ⊓ commutatorAction (D i) Za).map Za.subtype) at hh
    rw [hRmap] at hh
    convert hh using 1
    funext i
    rw [Subgroup.map_inf _ _ _ Za.subtype_injective, hRmap]
    change ⁅Za, z Γ cp.a'⁆ ⊓ (Vf i).map Za.subtype = _
    rw [(hVf i).1]
  refine ⟨r, D, Dlift, Vl, Vzero.map Za.subtype, J, Jlift, hJimage.symm, rfl,
    fun i => ⟨(hDimage i).symm, hVi i⟩, ?_, ?_, hSL, hVgen, hVambient, ?_, ?_, ?_, ?_⟩
  · exact hJoin.symm.trans hD.1
  · rw [← hJoin]
    exact hD
  · change Vzero.map Za.subtype = Za ⊓ Subgroup.centralizer (Y : Set H)
    have hh := w.fixedPoints_map_subtype Y hYP
    dsimp only at hh
    rw [hYimage] at hh
    exact hh
  · intro i
    change Nat.card ((Vf i).map Za.subtype) = 4
    rw [Subgroup.card_map_of_injective Za.subtype_injective]
    exact (hVf i).2
  · exact hRambient.1
  · exact hRambient

end Stellmacher.SectionEight
