module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallSubgroupSource
public import Theory.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The residual-nine obstruction from a maximal Sylow quotient

A nonnormal maximal Sylow subgroup is the unique maximal subgroup in its
minimal parabolic. Consequently the maximal subgroup is a two-group, its
odd residual is trivial, and its normal core is the ambient two-core.
The first source consumer derives all these local hypotheses before
applying the literal subgroup small-action obstruction.

The quotient consumer pulls a maximal Sylow back through a two-group
kernel and identifies that kernel with the two-core when the target has
trivial two-core. It transports the residual of order nine through the
resulting quotient equivalence. This is the H₀ lifting step in
Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem maximal_sylow_source_data
    (S : Sylow 2 G) (hS : IsCoatom (S : Subgroup G)) (hn : ¬(S : Subgroup G).Normal) :
    ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
      ChapterB.minimalParabolicMax S hP = (S : Subgroup G) ∧
      ChapterB.minimalParabolicCore S hP = pCore 2 G := by
  have hP : ChapterB.IsMinimalParabolicOver S ⊤ := by
    apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
    refine ⟨⟨S,⟨hS,le_rfl⟩,?_⟩,hn⟩
    intro M hM
    rcases hM.2.eq_or_lt with he | he
    · exact he.symm
    · exact (hM.1.ne_top (hS.2 M he)).elim
  have hm : ChapterB.minimalParabolicMax S hP = (S : Subgroup G) :=
    (ChapterB.minimalParabolicMax_unique S hP hS le_rfl).symm
  refine ⟨hP,hm,le_antisymm ?_ (ChapterB.minimalParabolicTwoCore_le_core S hP)⟩
  apply le_sSup
  refine ⟨inferInstance,?_⟩
  exact S.isPGroup'.to_le (by
    change (ChapterB.minimalParabolicMax S hP).normalCore ≤ S
    rw [hm]
    exact normalCore_le _)

variable {H D A : Type*} [Group H] [Finite H] [Group D] [Finite D]
  [Group A] [Finite A] {V U : Subgroup H} [IsElementaryAbelian 2 V]
/-- A solvable local subgroup with maximal nonnormal Sylow and residual nine
contradicts the original small-action hypotheses. -/
theorem source_subgroup_small_maximal_sylow_false
    {κ : GroupClass} (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hVT : V ≤ T) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (L : Subgroup H) (hVL : V ≤ L) (hLn : pCore 2 H ≤ normalizer (L : Set H))
    (S : Sylow 2 L) (hST : (S : Subgroup L).map L.subtype ≤ T)
    (hs : Group.IsSolvable L) (hS : IsCoatom (S : Subgroup L))
    (hn : ¬(S : Subgroup L).Normal)
    (hout : ¬ V.subgroupOf L ≤ pCore 2 L)
    (h9 : Nat.card (pResidual 2 (L ⧸ pCore 2 L)) = 9) : False := by
  obtain ⟨hP,hm,hJ⟩ := maximal_sylow_source_data S hS hn
  have hTS : (T : Subgroup H).subgroupOf L = S :=
    S.is_maximal' T.isPGroup'.comap_subtype (map_le_iff_le_comap.mp hST)
  have hVS : V.subgroupOf L ≤ S := by rw [←hTS]; exact comap_mono hVT
  have hcore : V.subgroupOf L ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2 := by
    rw [hm]
    exact hVS.trans (le_pCoreIn_of_normalizes S.isPGroup' le_rfl (S : Subgroup L).le_normalizer)
  have hres : (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
      (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (V.subgroupOf L : Set L) := by
    rw [hm]
    have hb : pResidual 2 (S : Subgroup L) = ⊥ := by
      apply le_bot_iff.mp
      exact sInf_le ⟨inferInstance, S.isPGroup'.of_surjective
        (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)⟩
    rw [hb,Subgroup.map_bot]
    exact bot_le
  exact source_subgroup_small_residual_nine_false hH T hVT hvn hfit hV hTU hU
    f hf hk hD hratio L hVL hLn S hST hP hs hcore (hJ ▸ hout) hres hJ h9

/-- Lift the concrete residual-nine quotient obstruction through its actual
two-group kernel, using the original action and chosen Sylow subgroup. -/
theorem source_subgroup_small_sylow_quotient_false
    {κ : GroupClass} (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hVT : V ≤ T) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (L : Subgroup H) (hVL : V ≤ L) (hLn : pCore 2 H ≤ normalizer (L : Set H))
    (S : Sylow 2 L) (hST : (S : Subgroup L).map L.subtype ≤ T)
    (g : L →* A) (hg : Function.Surjective g) (hg2 : IsPGroup 2 g.ker)
    (hA : Group.IsSolvable A) (hO : pCore 2 A = ⊥)
    (hP : IsCoatom ((S : Subgroup L).map g))
    (hPn : ¬((S : Subgroup L).map g).Normal)
    (hout : ¬ V.subgroupOf L ≤ g.ker)
    (h9 : Nat.card (pResidual 2 A) = 9) : False := by
  have hks : g.ker ≤ (S : Subgroup L) := hg2.le_sylow_of_normal S
  have hS : IsCoatom (S : Subgroup L) := by
    have hh := isCoatom_comap_of_surjective hg hP
    rwa [comap_map_eq_self hks] at hh
  have hn : ¬ (S : Subgroup L).Normal := fun hh => hPn (Normal.map hh g hg)
  have he : g.ker = pCore 2 L := by
    simpa only [hO,MonoidHom.comap_bot] using g.comap_pCore_of_ker_isPGroup hg hg2
  let : Group.IsNilpotent g.ker := hg2.isNilpotent
  let := hA
  have hs : Group.IsSolvable L :=
    Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [range_subtype])
  let e : (L ⧸ pCore 2 L) ≃* A := QuotientGroup.liftEquiv (pCore 2 L) (φ := g) hg he.symm
  have h9' : Nat.card (pResidual 2 (L ⧸ pCore 2 L)) = 9 := by
    let er := ((pResidual 2 (L ⧸ pCore 2 L)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))
    exact (Nat.card_congr er.toEquiv).trans h9
  exact source_subgroup_small_maximal_sylow_false hH T hVT hvn hfit hV hTU hU
    f hf hk hD hratio L hVL hLn S hST hs hS hn (he ▸ hout) h9'
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
