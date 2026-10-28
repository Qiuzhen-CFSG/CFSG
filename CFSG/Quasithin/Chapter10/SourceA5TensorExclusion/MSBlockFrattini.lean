module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSNaturalLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreRecognition

/-!
# The original tensor component in the Frattini-small branch

The original tensor overgroup hypotheses supply the MS characteristic condition,
faithful central orbit, and literal simple Sp4(4) quotient. If its commutator
core lies in Φ(O₂(H))Ω₁(Z(O₂(H))), the complete intrinsic block conclusion
follows; no additional model, elementary-abelian, or irreducibility hypotheses
are needed. This is the first branch of MS93 (3.6), as used in C.1.32.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Complete block recognition for the actual component in the source's
Frattini-small case. -/
theorem source_tensor_sp4_block_of_frattini_small
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g)
    (hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔
        omegaCenterIn (pCore 2 H)) : ChapterC.IsSp4FourBlock K := by
  let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
  let B := K.map (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D hn H hRH hLH hout hs K hK hF eK hfit hprod
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  obtain ⟨_,hfaith,_⟩ :=
    source_tensor_sp4_msCentralOrbit D hn H hRH hLH hout hs K hK hF eK hfit hprod
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  have hRne : R ≠ ⊥ := fun hr =>
    hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  exact ChapterC.RankTwo.Sp4Four.block_of_frattini_small_ms K R hK hfit hms
    hodd.isPGroup hRne hodd.twoCore_le hself hfaith hc hBC hsq hsmall

end CFSG.Quasithin.Chapter10
