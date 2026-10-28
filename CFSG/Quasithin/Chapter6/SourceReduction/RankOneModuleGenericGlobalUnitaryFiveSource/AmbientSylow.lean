module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedSylowOrders
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OuterSylow

/-!
# Ambient Sylow placement for represented U₅(4) involutions

The full saturated centralizer in the same extension, transported through
the actual reversed endpoint map, controls every two-subgroup of the ambient
involution centralizer. The fixed-Sylow normalizer bound then proves that the
whole original `C_T(t)` is ambient Sylow, retaining its outer elements. Its
proved order bound gives a conditional contradiction to an outer involution,
so the original equality `S = T` follows once the selected actor is
represented by a unitary twist.

Source: Aschbacher--Smith F.4.37--38, printed pp.293--294 of
`refs/quasithin.pdf`; the original chosen-module application is in 12.2.22,
p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem fixed_sylow_of_saturated_endpoint
    {X : Type*} [Group X] [Finite X] (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (φ : M →* X) (hφ : Function.Injective φ)
    (t : G) (ht : t ∈ (T : Subgroup G))
    (R : Sylow 2 (centralizer ({φ ⟨t,hTM ht⟩} : Set X)))
    (hsat : (R : Subgroup _).map (centralizer ({φ ⟨t,hTM ht⟩} : Set X)).subtype =
      ((T : Subgroup G).subgroupOf M).map φ ⊓ centralizer ({φ ⟨t,hTM ht⟩} : Set X))
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤ M) :
    ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup _).map (centralizer ({t} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({t} : Set G) := by
  let Q := (T : Subgroup G) ⊓ centralizer ({t} : Set G)
  let C := centralizer ({t} : Set G)
  let CE := centralizer ({φ ⟨t,hTM ht⟩} : Set X)
  have hQM : Q ≤ M := inf_le_left.trans hTM
  let ψ : Q →* X := φ.comp (inclusion hQM)
  have hψ : Function.Injective ψ := hφ.comp (inclusion_injective hQM)
  have himage : ψ.range = ((T : Subgroup G).subgroupOf M).map φ ⊓ CE := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      refine ⟨⟨⟨y.val,hQM y.property⟩,y.property.1,rfl⟩,?_⟩
      apply mem_centralizer_singleton_iff.mpr
      change φ ⟨y.val,hQM y.property⟩ * φ ⟨t,hTM ht⟩ =
        φ ⟨t,hTM ht⟩ * φ ⟨y.val,hQM y.property⟩
      rw [←map_mul,←map_mul]
      apply congrArg φ
      exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property.2)
    · rintro ⟨⟨a,ha,rfl⟩,hx⟩
      have hac : a.val ∈ C := mem_centralizer_singleton_iff.mpr (by
        have he := mem_centralizer_singleton_iff.mp hx
        rw [←map_mul,←map_mul] at he
        exact congrArg (fun a : M => a.val) (hφ he))
      exact ⟨⟨a.val,ha,hac⟩,rfl⟩
  have hcard : Nat.card R = Nat.card Q := by
    have hh := congrArg (fun B : Subgroup X => Nat.card B) (hsat.trans himage.symm)
    rw [card_map_of_injective CE.subtype_injective] at hh
    exact hh.trans (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hmax (B : Subgroup G) (hB : IsPGroup 2 B) (hQB : Q ≤ B)
      (hBC : B ≤ C) (hBM : B ≤ M) : B = Q := by
    let χ : B →* CE := (φ.comp (inclusion hBM)).codRestrict CE (fun b => by
      apply mem_centralizer_singleton_iff.mpr
      change φ ⟨b.val,hBM b.property⟩ * φ ⟨t,hTM ht⟩ =
        φ ⟨t,hTM ht⟩ * φ ⟨b.val,hBM b.property⟩
      rw [←map_mul,←map_mul]
      apply congrArg φ
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hBC b.property)))
    have hχ : Function.Injective χ := by
      intro x y he
      exact Subtype.ext (congrArg (fun a : M => a.val) (hφ (congrArg Subtype.val he)))
    obtain ⟨P,hP⟩ := (hB.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective).exists_le_sylow
    have hc : Nat.card B ≤ Nat.card R := by
      rw [Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv]
      exact (card_le_of_le hP).trans_eq (Nat.card_congr (P.equiv R).toEquiv)
    exact (eq_of_le_of_card_ge hQB (hcard ▸ hc)).symm
  obtain ⟨P,hP⟩ := ((T.isPGroup'.to_le (show Q ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := C)).exists_le_sylow
  refine ⟨P,?_⟩
  apply prime_overgroup_eq_of_normalizer_control Q C M hn hmax
    ((P : Subgroup C).map C.subtype) (P.isPGroup'.map C.subtype)
  · rw [←map_subgroupOf_eq_of_le (show Q ≤ C from inf_le_right)]
    exact map_mono hP
  · exact map_subtype_le _


variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

theorem Preparation.unitaryFive_represented_fixed_ambient_sylow
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (P : Sylow 2 r.extension.middle)
    (hP : (P : Subgroup r.extension.middle) =
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (hinner : (P : Subgroup r.extension.middle) ⊓
      (inner U.Carrier).comap r.extension.middle.subtype =
      ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)))
    (htT : t.val ∈ (T : Subgroup G))
    (ht : orderOf t=2) (u : U.form.unitarySubgroup)
    (hf : (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (hfull : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (centralizer ({j (F.middle t)} : Set r.extension.carrier)),
        (R : Subgroup _).map (centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            centralizer ({j (F.middle t)} : Set r.extension.carrier))
    (hsat : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (R : Subgroup _).map (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) :
    ∃ Q : Sylow 2 (centralizer ({t.val} : Set G)),
      (Q : Subgroup _).map (centralizer ({t.val} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let M := normalizer (residual H : Set G)
  have hTM : (T : Subgroup G) ≤ M := hH.1.1.2.trans (le_normalizer_residual H)
  have hTD : (T : Subgroup G) ≤ D := le_inf h.sylow_normalizes hTM
  let j := inclusion (inf_le_left.trans r.extension.left_le : r.extension.middle ≤ r.extension.carrier)
  let φ : M →* r.extension.carrier :=
    (inclusion r.extension.left_le).comp F.right.toMonoidHom
  have hφ : Function.Injective φ := (inclusion_injective r.extension.left_le).comp F.right.injective
  have hcomm (x : D) : φ ⟨x.val,x.property.2⟩ = j (F.middle x) := by
    change inclusion r.extension.left_le
      (F.right ((UnitaryCompletion.normalizerDiagram L (residual H)).right x)) = j (F.middle x)
    calc
      _ = inclusion r.extension.left_le
          ((r.extension.amalgam.reverse).right (F.middle x)) :=
            congrArg (inclusion r.extension.left_le) (F.right_commutes x)
      _ = j (F.middle x) := rfl
  have hmap : ((T : Subgroup G).subgroupOf M).map φ = (P : Subgroup r.extension.middle).map j := by
    rw [hP]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      let z : D := ⟨y.val,hTD hy⟩
      exact ⟨F.middle z,⟨z,hy,rfl⟩,(hcomm z).symm⟩
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨⟨z.val,hTM hz⟩,hz,hcomm z⟩
  have htf : φ ⟨t.val,hTM htT⟩ = j (F.middle t) := hcomm t
  have hs : ∃ R : Sylow 2 (centralizer ({φ ⟨t.val,hTM htT⟩} : Set r.extension.carrier)),
      (R : Subgroup _).map (centralizer ({φ ⟨t.val,hTM htT⟩} : Set r.extension.carrier)).subtype =
        ((T : Subgroup G).subgroupOf M).map φ ⊓
          centralizer ({φ ⟨t.val,hTM htT⟩} : Set r.extension.carrier) := by
    have hcent : centralizer ({φ ⟨t.val,hTM htT⟩} : Set r.extension.carrier) =
        centralizer ({j (F.middle t)} : Set r.extension.carrier) := by rw [htf]
    dsimp only at hfull
    rw [← hcent, ← hmap] at hfull
    exact hfull
  obtain ⟨R,hR⟩ := hs
  exact fixed_sylow_of_saturated_endpoint M hTM φ hφ t.val htT R hR
    (d.unitaryFive_represented_fixed_normalizer_le_right h hH hp U hc
      r F P hinner t htT ht u hf hsat)

theorem Preparation.unitaryFive_represented_outer_contradiction
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (P : Sylow 2 r.extension.middle)
    (hP : (P : Subgroup r.extension.middle) =
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (hinner : (P : Subgroup r.extension.middle) ⊓
      (inner U.Carrier).comap r.extension.middle.subtype =
      ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)))
    (htT : t.val ∈ (T : Subgroup G))
    (ht : orderOf t=2) (u : U.form.unitarySubgroup)
    (hf : (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (hfull : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (centralizer ({j (F.middle t)} : Set r.extension.carrier)),
        (R : Subgroup _).map (centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            centralizer ({j (F.middle t)} : Set r.extension.carrier))
    (hsat : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (R : Subgroup _).map (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) :
    False := by
  have hno := (d.unitaryFive_represented_fixed_sylow_orders h hH hp U hc
    r F P hinner t ht u hf hsat).2.2
  exact hno (d.unitaryFive_represented_fixed_ambient_sylow h hH hp U hc
    r F P hP hinner t htT ht u hf hfull hsat)

/-- Only the concrete representation of the same original actor remains
as an earlier premise. Selection discharges both saturation clauses. -/
theorem Preparation.unitaryFive_sourceS_eq_sylow_of_actor_representation
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (hrep : ∀ (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
      (ell : UnitaryNativeLift.Five.LiftReverse U a)
      (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse),
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) →
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) →
      (∀ z, (F.middle z).val = (ell.action z).val) →
      ∀ t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)),
        t.val ∈ (T : Subgroup G) → orderOf t=2 → t.val ∉ sourceS L H →
        ∃ u : U.form.unitarySubgroup,
          (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    sourceS L H = (T : Subgroup G) := by
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  by_contra hne
  obtain ⟨a,ell,F,h0,h1,hD,_,_,_,_,P,hP,hinner,t,htT,ht,ho,_,_,hfull,hsat⟩ :=
    d.unitaryFive_marked_outer_saturated h hH hp U hc r (lt_of_le_of_ne hST hne)
  obtain ⟨u,hf⟩ := hrep a ell F h0 h1 hD t htT ht ho
  exact d.unitaryFive_represented_outer_contradiction h hH hp U hc
    r F P hP hinner t htT ht u hf hfull hsat

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
