module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalModule
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalDecomposition
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductSeed

/-!
# TerminalModule at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalModule`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterB.SourceInduction

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

private theorem K_le_Y_at : P.K ≤ P.Y := le_sup_left.trans le_sup_left

private theorem L2_le_Y_at : P.L2 ≤ P.Y := le_sup_right.trans le_sup_left

private theorem commutator_map_at (X : Subgroup G) (hX : X ≤ P.Y) :
    (⁅P.U.subgroupOf P.Y,X.subgroupOf P.Y⁆).map P.Y.subtype = ⁅P.U,X⁆ := by
  rw [map_commutator,map_subgroupOf_eq_of_le P.U_le_Y,map_subgroupOf_eq_of_le hX]

private theorem module_eq_seed_at (A : P.ProductAnalysis) (X B : Subgroup G)
    (hX : X ≤ P.Y) (hB : B ≤ P.Y)
    (hn : ((B.subgroupOf P.Y).map
      (A.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y)))).Normal)
    (hgenerates : X ⊔ B ⊔ (T : Subgroup G) = P.Y)
    (hcross : X ≤ centralizer (⁅P.U,B⁆ : Subgroup G)) : ⁅P.U,B⁆ = ⁅P.Z,B⁆ := by
  let q := QuotientGroup.mk' (pCore 2 P.Y)
  let U₀ := P.U.subgroupOf P.Y
  let Z₀ := P.Z.subgroupOf P.Y
  let K₀ := X.subgroupOf P.Y
  let B₀ := B.subgroupOf P.Y
  let T₀ := (T : Subgroup G).subgroupOf P.Y
  have hn' : ((B₀.map q).map A.quotient.toMonoidHom).Normal := by
    rw [map_map]
    change ((B.subgroupOf P.Y).map
      (A.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y)))).Normal
    exact hn
  let : (B₀.map q).Normal := hn'.of_map_injective A.quotient.injective
  have hZU : Z₀ ≤ U₀ := fun _ hz => le_componentOrbit P.Z P.Y hz
  have hspan : U₀ = conjugateSpanBy Z₀ ⊤ := by
    apply map_injective P.Y.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le P.U_le_Y,
      map_subgroupOf_eq_of_le P.Z_le_Y,←MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer P.Z P.Y _
        (le_conjugateSpanBy P.Z P.Y) (le_normalizer_conjugateSpanBy P.Z P.Y)
    · exact conjugateSpanBy_le (le_componentOrbit P.Z P.Y)
        (le_normalizer_componentOrbit P.Z P.Y)
  have hgen : K₀ ⊔ B₀ ⊔ T₀ = ⊤ := by
    apply map_injective P.Y.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hB,map_subgroupOf_eq_of_le P.sylow_le_Y,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgenerates
  have hTZ : T₀ ≤ centralizer (Z₀ : Set P.Y) := by
    intro t ht z hz
    exact Subtype.ext (((mem_omegaCenterIn_iff _ _).mp hz).2.1 t ht).symm
  have hKW : K₀ ≤ centralizer ((⁅U₀,B₀⁆ : Subgroup P.Y) : Set P.Y) := by
    intro k hk x hx
    apply Subtype.ext
    apply hcross hk x
    rw [←P.commutator_map_at B hB]
    exact mem_map_of_mem P.Y.subtype hx
  have he := conjugateSpan_commutator_eq_seed Z₀ U₀ K₀ B₀ T₀ q
    (show q.ker ≤ centralizer (U₀ : Set P.Y) from
      ((QuotientGroup.ker_mk' _).trans (P.module_centralizer_eq A).symm).le)
    hZU hspan hgen hTZ hKW
  have hm := congrArg (map P.Y.subtype) he
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le P.U_le_Y,
    map_subgroupOf_eq_of_le P.Z_le_Y,map_subgroupOf_eq_of_le hB] at hm
  exact hm

theorem false_of_module_analysis_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : P.ProductAnalysis) : False :=
  P.false_of_module_decomposition_at structural A (P.module_moved_disjoint A)
    (P.K_le_Y_at.trans (P.module_second_normalized A)) (P.module_second_eq_seed A)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

