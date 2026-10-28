module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.BlockLayer
public import CFSG.Quasithin.Chapter13.Section07.SourceCover
/-!
# The original A₆ block and the actual plane normalizer

The established covered-A₆ source supplies quasisimplicity, removing that
premise from the literal C.1.24 application. Quasithinness bounds the ternary
rank of the actual plane normalizer by two, exactly as needed for the two-A₃
residual calculation. Finally, an element of N_G(L) normalizing any nontrivial
subspace of V normalizes V itself: transport one nonzero vector through the
transitive original L action.

Source: Aschbacher--Smith 13.5.6, printed p.917. The prior unique maximal
two-local theorem and selected normalizer escape remain explicit here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_plane_normalizer_rank (W:Subgroup G)(hcard:Nat.card W=4) :
    primeRank 3 (normalizer (W:Set G))≤2 := by
  have hn:W≠⊥ := by
    intro hz
    have hh:Nat.card W=1:=by rw [hz];exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
    omega
  exact isQuasithin_iff_twoLocal.mp d.counterexample.qtke.quasithin
    (normalizer (W:Set G)) ⟨W,hn,IsPGroup.of_card (p:=2) (n:=2) hcard,rfl⟩
    3 Nat.prime_three (by decide)

theorem source_local_plane_normalizer_rank (W:Subgroup G)(hcard:Nat.card W=4) :
    primeRank 3 (M⊓normalizer (W:Set G):Subgroup G)≤2 :=
  (primeRank_mono 3 inf_le_right).trans (source_plane_normalizer_rank d W hcard)

/-- The final literal input to the two-A₃ calculation; the earlier
quasisimplicity input is supplied by the original covered-A₆ source. -/
theorem source_block_with_rank
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0)
    (he:¬normalizer (planeCentralizer (T:=T) W:Set G)≤M) :
    ChapterC.IsAlternatingBlock L 6 ∧
      (ChapterC.blockU L).map L.subtype=V ∧
      M≤normalizer (V:Set G) ∧ generalizedFitting M=pCore 2 M ∧
      primeRank 3 (M⊓normalizer (W:Set G):Subgroup G)≤2 := by
  obtain ⟨hb,hV,hM,hF⟩:=source_block_and_module d
    (Section07.source_core_quotient_quasisimple d) hu W hWV hcard hn he
  exact ⟨hb,hV,hM,hF,source_local_plane_normalizer_rank d W hcard⟩

/-- Fixing a nontrivial subspace of the natural module inside N_G(L)
already preserves the whole module. This uses actual L-transitivity. -/
theorem local_plane_normalizer_le_moduleNormalizer
    (W:Subgroup G)(hWV:W≤V)(hW:W≠⊥) :
    M⊓normalizer (W:Set G)≤normalizer (V:Set G) := by
  obtain ⟨w,hw,hw1⟩ : ∃w:G,w∈W∧w≠1 := by
    obtain ⟨w,hw⟩:=Subgroup.ne_bot_iff_exists_ne_one.mp hW
    exact ⟨w,w.property,fun hh=>hw (Subtype.ext hh)⟩
  apply le_normalizer_iff.mpr
  intro g hg v hv
  by_cases hv1:v=1
  · simp only [hv1,mul_one,mul_inv_cancel];exact V.one_mem
  obtain ⟨l,hl,hlv⟩:=Section07.natural_nonzero_transitive d (hWV hw) hv hw1 hv1
  have hgL:g∈normalizer (L:Set G):=d.local_normalizer ▸ hg.1
  have hgl:g*l*g⁻¹∈L:=mem_normalizer_iff.mp hgL l |>.mp hl
  have hgw:g*w*g⁻¹∈V:=hWV (mem_normalizer_iff.mp hg.2 w |>.mp hw)
  have hn:=d.normalizes_V (mem_sup_left hgl)
  have hh:=mem_normalizer_iff.mp hn (g*w*g⁻¹) |>.mp hgw
  convert hh using 1
  rw [←hlv]
  group

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
