module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FrattiniOrbit
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.OrbitDegree

/-!
# The original normal linear Bender field restriction

The selected closure U=⟨V^H⟩ supplies its literal Frattini quadratic space,
singular normalizer-fixed seed, and spanning H-orbit. The opposite elementary
subgroup bounds a singular codimension. The normal PSL₂ factor gives a marked
projective-line Borel and a faithful quotient action, so the orbit has size
2^f+1 and the codimension is at most f+1. Thus f=2 or f=3.

This is the numerical normal-linear step of Aschbacher–Smith 14.2.16,
printed pp.985–986. The Suzuki, unitary and global amalgam branches remain
separate source obligations.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The actual nonabelian source closure restricts its selected normal
linear Bender parameter to field orders four and eight. -/
theorem source_nonabelian_linear_degree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.2 : Subgroup H) = ⊤)
    (hcore : sourceKernel ((H ⊓ M).subgroupOf H) = pCore 2 H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F)) :
    n = 2 ∨ n = 3 := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,w,hw,hfix,hspan,hzero,hpolar⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH hne
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let B := SmallFrattini.quotientBilinearForm h.U_isPGroup hphic
  have hMN : M ≤ normalizer (D.V : Set G) :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1).le
  have hfixed (g : H) (hg : g ∈ (H ⊓ M).subgroupOf H) :
      ρ g (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D g w) = Additive.ofMul w
    exact congrArg Additive.ofMul (hfix g (hMN hg.2))
  obtain ⟨E,hE,A,hAU,hA,hindex⟩ :=
    source_nonabelian_elementary_image hG T hempty hM hu hmany hcard e H hH hne
  have hr := hm.linear_actor_two_rank (T.subtype hH.1.2) _ K hgen hcore hn hF
  have hEc : Nat.card E ≤ 2^n :=
    (primeRank_le_iff_elementary_card_le (H ⧸ pCore 2 H)).mp hr E hE
  let Ai := A.subgroupOf D.U
  let := hA
  let : IsElementaryAbelian 2 Ai :=
    IsElementaryAbelian.of_injective (p := 2) (subgroupOfEquivOfLe hAU).toMonoidHom
      (subgroupOfEquivOfLe hAU).injective
  have hi : Ai.index ≤ 2^(n+1) := by
    change A.relIndex (conjugateSpanBy (localModule T M) H) ≤ _
    rw [hindex,pow_succ]
    exact (Nat.mul_le_mul_left 2 hEc).trans_eq (Nat.mul_comm _ _)
  obtain ⟨W,hWq,hW,hWc⟩ := SmallFrattini.exists_totallySingular_of_index
    h.U_isPGroup hphic Ai (n+1) hi
  have hSM : (T.subtype hH.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  exact hm.linear_field_degree _ K _ hgen hSM n (by omega) hF ρ (Additive.ofMul w)
    hfixed hspan B (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul) W hW hWc
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
