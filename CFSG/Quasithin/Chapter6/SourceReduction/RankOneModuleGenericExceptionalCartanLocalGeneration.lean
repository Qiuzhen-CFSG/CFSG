module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightNatural
public import Theory.SpecificGroups.Alternating.SevenFiveRestriction

/-!
# The escaping cubic generates the maximal local join

The literal right residual has A₅ image in the faithful A₇ quotient. Its
join with the Sylow image is maximal. The cubic escapes the right group,
so adjoining it generates the whole quotient. The original right group
contains the two-core, allowing this generation to lift to K T itself.
This is the generation used in the characteristic-subgroup paragraph of
Aschbacher–Smith 5.1.13, printed p.638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Generation by the original right group and its escaping cubic. -/
theorem LocalA7Configuration.cubic_sup_right
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    H ⊔ D = K ⊔ (T : Subgroup G) := by
  let M := K ⊔ (T : Subgroup G)
  let R := (residual H).subgroupOf M
  let J := H.subgroupOf M
  let C := D.subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hRM : residual H ≤ M := (d.residual_le.trans a.contains).trans le_sup_left
  have hHM : H ≤ M := by
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le hRM le_sup_right
  have hDM : D ≤ M := ((d.cubic_le.trans inf_le_right).trans a.contains).trans le_sup_left
  obtain ⟨q,hq,_,hk,_,e,_,_⟩ := a.four_residual_natural h hH hgen c d
  have hfour : Nat.card SL2FourNatural.F = 4 := by
    rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let eR := e.trans ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=SL2FourNatural.F)).trans e5)
  have hPJ : (P : Subgroup M) ≤ J := fun _ hx => hH.1.1.2 hx
  have hRJ : R ⊔ (P : Subgroup M) = J := by
    apply map_injective M.subtype_injective
    change (R ⊔ (T : Subgroup G).subgroupOf M).map M.subtype = J.map M.subtype
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRM,map_subgroupOf_eq_of_le le_sup_right,
      map_subgroupOf_eq_of_le hHM,residual_sup_sylow T H hH.1.1.2]
  have hPN : (P : Subgroup M) ≤ normalizer (R : Set M) := by
    intro t ht
    exact mem_normalizer_iff.mpr (fun r => mem_normalizer_iff.mp
      (le_normalizer_residual H (hH.1.1.2 ht)) r.val)
  have hPq : ((P : Subgroup M).map q) ≤ normalizer (R.map q : Set (alternatingGroup (Fin 7))) :=
    (map_mono hPN).trans (R.le_normalizer_map q)
  have hm := Theory.SpecificGroups.Alternating.SevenFivePlacement.sylow_sup_five_isCoatom
    (R.map q) eR (P.mapSurjective hq) hPq
  have hJq : J.map q = R.map q ⊔ (P : Subgroup M).map q := by
    rw [←hRJ,Subgroup.map_sup]
  change IsCoatom (R.map q ⊔ (P : Subgroup M).map q) at hm
  rw [←hJq] at hm
  have hkerJ : q.ker ≤ J := (hk.symm ▸ pCore_isPGroup.le_sylow_of_normal P).trans hPJ
  have hn : ¬ C.map q ≤ J.map q := by
    intro hc
    have hCJ : C ≤ J := by
      have hh := map_le_iff_le_comap.mp hc
      rwa [comap_map_eq_self hkerJ] at hh
    apply d.cubic_escape
    have hDH : D ≤ H := by
      have hh := map_mono (f:=M.subtype) hCJ
      rwa [map_subgroupOf_eq_of_le hDM,map_subgroupOf_eq_of_le hHM] at hh
    exact hDH.trans (le_normalizer_residual H)
  have htop : (J ⊔ C).map q = ⊤ := by
    apply hm.2 _ (lt_of_le_of_ne (map_mono le_sup_left) ?_)
    intro he
    apply hn
    exact (map_mono (show C ≤ J ⊔ C from le_sup_right)).trans_eq he.symm
  have hfull : J ⊔ C = ⊤ := by
    have hh := comap_map_eq_self (show q.ker ≤ J ⊔ C from hkerJ.trans le_sup_left)
    rw [htop,comap_top] at hh
    exact hh.symm
  have hh := congrArg (map M.subtype) hfull
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hHM,map_subgroupOf_eq_of_le hDM,
    ←MonoidHom.range_eq_map,range_subtype] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
