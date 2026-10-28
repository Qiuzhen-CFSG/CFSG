module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FrattiniOrbit
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.SuzukiOrbit

/-!
# Exclusion of the original nonabelian normal Suzuki row

The selected closure U=⟨V^H⟩ supplies its literal Frattini space, a
normalizer-fixed seed with spanning orbit, and a nonzero invariant polar
form. Its opposite elementary subgroup has singular codimension at most
2m+2, using the automorphism two-rank of the normal Suzuki image. The
marked Borel orbit is the ovoid of size 2^(4m+2)+1. The invariant orbit
bound contradicts this size for every m ≥ 1.

This removes the normal Suzuki possibility from the nonabelian closure
branch preceding Aschbacher--Smith 14.2.16, printed pp.982--986, on the
original H/O₂(H) quotient and the same component/Borel marking.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The normal Suzuki row is impossible for the actual nonabelian source closure. -/
theorem source_nonabelian_suzuki_false
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
    (m : ℕ) (hmpos : 1 ≤ m)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K
      (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m)) : False := by
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
  have hr := hm.suzuki_actor_two_rank (T.subtype hH.1.2) _ K hgen hcore (by omega)
  have hEc : Nat.card E ≤ 2^(2*m+1) :=
    (primeRank_le_iff_elementary_card_le (H ⧸ pCore 2 H)).mp hr E hE
  let Ai := A.subgroupOf D.U
  let := hA
  let : IsElementaryAbelian 2 Ai :=
    IsElementaryAbelian.of_injective (p := 2) (subgroupOfEquivOfLe hAU).toMonoidHom
      (subgroupOfEquivOfLe hAU).injective
  have hi : Ai.index ≤ 2^((2*m+1)+1) := by
    change A.relIndex (conjugateSpanBy (localModule T M) H) ≤ _
    rw [hindex,pow_succ]
    exact (Nat.mul_le_mul_left 2 hEc).trans_eq (Nat.mul_comm _ _)
  obtain ⟨W,hWq,hW,hWc⟩ := SmallFrattini.exists_totallySingular_of_index
    h.U_isPGroup hphic Ai ((2*m+1)+1) hi
  have hSM : (T.subtype hH.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  have hmark : ModelBorelPair ((H ⊓ M).subgroupOf H) K
      (MulAction.stabilizer (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
        (BenderSuzuki.MatrixGroups.suzukiOvoidInfinity m)) := by
    simpa only [BenderSuzuki.MatrixGroups.suzukiBorelSubgroup_eq_stabilizer m (by omega)] using hm
  have hb := hmark.orbit_degree_bound _ K _ hgen hSM
    (BenderSuzuki.MatrixGroups.suzukiOvoidInfinity m)
    (BenderSuzuki.MatrixGroups.suzukiOvoid_two_pretransitive m)
    ρ (Additive.ofMul w) hfixed hspan B
    (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul)
    W hW ((2*m+1)+1) hWc
  rw [BenderSuzuki.MatrixGroups.suzukiOvoid_card] at hb
  have hdegree : 2*m+2 ≤ 2^(2*m+1) := Nat.lt_two_pow_self
  have hlarge : 2 < 2^(2*m+1) := by
    calc
      2 = 2^1 := by decide
      _ < 2^(2*m+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hbound : 2*(2*m+2) < (2^(2*m+1))^2 := by
    have hmul := Nat.mul_le_mul_left 2 hdegree
    nlinarith
  omega
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
