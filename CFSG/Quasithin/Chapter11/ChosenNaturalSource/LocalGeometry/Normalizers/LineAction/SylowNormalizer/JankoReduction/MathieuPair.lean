module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.CentralCover
public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers.Geometry
public import Theory.Mathieu.M23.Properties.UniqueNormalFour
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu

/-!
# Sylow normalizers in the M₂₂ and M₂₃ component rows

The two elementary sixteen-subgroups of the marked M₂₃ Sylow have an
intrinsic intersection. Its fixed heptad is therefore preserved by the
Sylow normalizer. The actual heptad action has two-group kernel and A₇
quotient; self-normalization of Sylows in A₇ lifts to M₂₃. The odd-index
point-stabilizer embedding then gives the same equality for M₂₂.
Together with the proved outer two-group bounds, these identities exclude
both component quotients and the M₂₂ central-cover row in the actual source
configuration. Source: Aschbacher–Smith 3.3.12 (**), p.589, and GLS3
Tables 5.3c–d. Final recognition remains with qt-d-1222-natural-line-action.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem mathieu_twentyThree_marked_normalizer :
    normalizer (Sporadic.Mathieu.M23Geometry.FusionCertificate.subgroup :
      Set Sporadic.Mathieu.M23) = Sporadic.Mathieu.M23Geometry.FusionCertificate.subgroup := by
  open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
    Sporadic.Mathieu.M23Geometry.FusionCertificate
    Sporadic.Mathieu.M23Geometry.ElementarySylow in
    let P := FusionCertificate.sylow
    let H := MulAction.stabilizer M23 FourNormalizers.fixedSet
    have hN : normalizer (subgroup : Set M23) ≤ H := by
      apply le_trans ?_ FourNormalizers.normalizer_le_stabilizer
      intro g hg
      apply mem_normalizer_iff_map_conj_eq.mpr
      let a := MulAut.conj g
      have ha : subgroup.map a.toMonoidHom = subgroup := mem_normalizer_iff_map_conj_eq.mp hg
      have himage (i : Fin 2) : ∃ j, (candidate i).map a.toMonoidHom = candidate j := by
        apply card16_eq_candidate
        · let := candidate_elementary i
          exact IsElementaryAbelian.map a.toMonoidHom
        · rw [card_map_of_injective a.injective,candidate_card]
        · exact (map_mono (candidate_le_sylow i)).trans_eq ha
      obtain ⟨i,hi⟩ := himage 0
      obtain ⟨j,hj⟩ := himage 1
      have hne : i ≠ j := by
        intro he
        have hc : candidate 0 = candidate 1 := map_injective a.injective
          (hi.trans (he ▸ hj.symm))
        have hh := common_card
        rw [common,hc,inf_idem,candidate_card] at hh
        norm_num at hh
      change (candidate 0 ⊓ candidate 1).map a.toMonoidHom = candidate 0 ⊓ candidate 1
      rw [map_inf _ _ _ a.injective,hi,hj]
      fin_cases i <;> fin_cases j <;> simp_all [inf_comm]
    have hPH : (P : Subgroup M23) ≤ H := (P : Subgroup M23).le_normalizer.trans hN
    let R := P.subtype hPH
    obtain ⟨q,hq,hker⟩ := (heptad_stabilizer_local_structure
      FourNormalizers.fixedSet_mem (MulEquiv.refl _)).2.2
    let Q := R.mapSurjective hq
    have hk : q.ker ≤ (R : Subgroup H) := hker.le_sylow_of_normal R
    have hlocal : normalizer (R : Set H) ≤ (R : Subgroup H) := by
      have hh := ((R : Subgroup H).le_normalizer_map q).trans
        (AlternatingSevenSylow.sylow_normalizer_eq_self Q).le
      have hh' := map_le_iff_le_comap.mp hh
      change normalizer (R : Set H) ≤ ((R : Subgroup H).map q).comap q at hh'
      rwa [comap_map_eq_self hk] at hh'
    apply le_antisymm ?_ le_normalizer
    intro g hg
    let g' : H := ⟨g,hN hg⟩
    apply hlocal (x := g')
    change g' ∈ normalizer ((P : Subgroup M23).subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hPH]
    exact hg

private theorem mathieu_twentyThree_self_normalizing (Q : Sylow 2 Sporadic.Mathieu.M23) :
    normalizer (Q : Set Sporadic.Mathieu.M23) = (Q : Subgroup Sporadic.Mathieu.M23) := by
  open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry in
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 FusionCertificate.sylow Q
    have he : FusionCertificate.subgroup.map (MulAut.conj g).toMonoidHom =
        (Q : Subgroup M23) := congrArg Sylow.toSubgroup hg
    change normalizer ((Q : Subgroup M23) : Set M23) = _
    rw [←he,←map_equiv_normalizer_eq,mathieu_twentyThree_marked_normalizer]

private theorem mathieu_twentyTwo_self_normalizing (P : Sylow 2 Sporadic.Mathieu.M22) :
    normalizer (P : Set Sporadic.Mathieu.M22) = (P : Subgroup Sporadic.Mathieu.M22) := by
  open Sporadic.Mathieu in
    let f : M22 →* M23 := (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
      m23EquivM22PointStabilizer.toMonoidHom
    have hf : Function.Injective f := Subtype.val_injective.comp m23EquivM22PointStabilizer.injective
    obtain ⟨Q,hPQ⟩ := (P.isPGroup'.map f).exists_le_sylow
    have hPcard : Nat.card P = 128 := by
      rw [P.card_eq_multiplicity,m22_order]
      decide +kernel
    have hQcard : Nat.card Q = 128 := by
      rw [Q.card_eq_multiplicity,m23_order]
      decide +kernel
    have hPQeq : (P : Subgroup M22).map f = (Q : Subgroup M23) :=
      eq_of_le_of_card_ge hPQ (by rw [card_map_of_injective hf,hPcard,hQcard])
    apply le_antisymm ?_ (P : Subgroup M22).le_normalizer
    apply (map_le_map_iff_of_injective hf).mp
    have hh := (P : Subgroup M22).le_normalizer_map f
    rw [hPQeq] at hh
    exact (hh.trans (mathieu_twentyThree_self_normalizing Q).le).trans_eq hPQeq.symm

private theorem mathieu_twentyTwo_outer_two :
    IsPGroup 2 (MulAut.Outer Sporadic.Mathieu.M22) :=
  Chapter1.XiEmbedding.OuterModels.m22_outer_isPGroup_two_of_coverage
    Sporadic.Mathieu.m22DesignAutToAut_surjective

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The M₂₂ quotient is incompatible with the nontrivial odd Sylow action. -/
theorem quotient_not_mathieu_twentyTwo :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Sporadic.Mathieu.M22) :=
  E.quotient_not_equiv_self_normalizing_outer_two
    mathieu_twentyTwo_self_normalizing mathieu_twentyTwo_outer_two

/-- The M₂₃ quotient is incompatible with the same literal action. -/
theorem quotient_not_mathieu_twentyThree :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃* Sporadic.Mathieu.M23) :=
  E.quotient_not_equiv_self_normalizing_outer_two
    mathieu_twentyThree_self_normalizing Sporadic.Mathieu.m23_outer_isTwoGroup

/-- Perfectness makes the central-quotient action faithful, so the actual
M₂₂ triple-cover row is excluded as well. -/
theorem quotient_not_mathieu_cover :
    ¬ Chapter1.Section02.LocalModels.IsM22Cover (E.component ⧸ pCore 2 E.component) := by
  rintro ⟨_,_,⟨e⟩⟩
  exact E.false_of_central_quotient_stabilizers e (fun P =>
    MulAut.isPGroup_sylow_stabilizer_of_self_normalizing P
      (mathieu_twentyTwo_self_normalizing P) mathieu_twentyTwo_outer_two)

end MovedComponent
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
