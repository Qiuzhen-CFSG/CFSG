module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FrattiniOrbit
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.UnitaryOrbit

/-!
# Excluding the normal unitary row in the nonabelian source closure

The original plane-orbit construction gives a spanning Borel-fixed vector
in the binary Frattini quotient. The opposite elementary subgroup gives a
totally singular subspace of codimension at most n+2 once the ambient
actor quotient has two-rank at most n+1. The literal PSU₃ isotropic-point
orbit then contradicts the nonzero polar form.

The rank transfer retains the possible central-three SU₃ cover; no equality
between the normal core of H∩M and O₂(H) is assumed here.
Source: the normal Bender branch preceding Aschbacher–Smith 14.2.16,
printed pp.985–986.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The normal unitary row contradicts the original nonabelian closure. -/
theorem source_nonabelian_unitary_false_of_rank
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
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = (2^n)^2)
    (hfieldFixed : Nat.card {x : F // J.conj x = x} = 2^n)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K (unitaryBorel J hJ))
    (hr : primeRank 2 (H ⧸ pCore 2 H) ≤ n+1) : False := by
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
  have hEc : Nat.card E ≤ 2^(n+1) :=
    (primeRank_le_iff_elementary_card_le (H ⧸ pCore 2 H)).mp hr E hE
  let Ai := A.subgroupOf D.U
  let := hA
  let : IsElementaryAbelian 2 Ai :=
    IsElementaryAbelian.of_injective (p := 2) (subgroupOfEquivOfLe hAU).toMonoidHom
      (subgroupOfEquivOfLe hAU).injective
  have hi : Ai.index ≤ 2^(n+2) := by
    change A.relIndex (conjugateSpanBy (localModule T M) H) ≤ _
    rw [hindex,pow_succ]
    exact (Nat.mul_le_mul_left 2 hEc).trans_eq (Nat.mul_comm _ _)
  obtain ⟨W,hWq,hW,hWc⟩ := SmallFrattini.exists_totallySingular_of_index
    h.U_isPGroup hphic Ai (n+2) hi
  have hSM : (T.subtype hH.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  exact hm.unitary_polar_false J hJ _ K _ hgen hSM n hn hF hfieldFixed ρ (Additive.ofMul w)
    hfixed hspan B (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul) W hW hWc
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
