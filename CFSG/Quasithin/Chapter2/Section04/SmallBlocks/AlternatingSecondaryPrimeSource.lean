module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryResidualSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullCentralizerSource
public import Theory.SpecificGroups.PSL2.AlternatingFourActorCentralizer
/-!
# Excluding the prime rows in the original secondary centralizer

The original fixed four contains a literal element fused to the central
involution z and commuting with the residual A₄. Its faithful canonical
action on a normal component forces that element to centralize the component
in both PSL₂(7) and PSL₂(17). Fusion then makes the component order divide
|C_G(z)| = 2304, contradicting the prime-field order formula.

The final consumer retains the same affine marking, residual packet and
ordinary component. It derives C_G(z) = M and its order from the original
marked center and maximal-centralizer source results.

Source: Aschbacher--Smith, proof of 2.4.29, printed p.546. The prime-field
actor centralizer gives a common exclusion of both rows without the separate
Thompson-subgroup argument used there for PSL₂(17).
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2

variable {G : Type*} [Group G] [Finite G]

/-- The original fused fixed element excludes both remaining prime-field rows. -/
theorem secondary_prime_component_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({u}:Set G)) P M z)
    (L K : Subgroup (centralizer ({u}:Set G))) [K.Normal]
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u}:Set G)) K)
    (eA : L≃*alternatingGroup (Fin 4))
    (a : L) (ha : a∈pCore 2 L) (hza : z=(a:G)*u)
    {p : ℕ} [Fact p.Prime] (hp : p=7 ∨ p=17) (eK : K≃*PSL(2,ZMod p))
    (v : centralizer ({u}:Set G)) (hv : v∈centralizer (L : Set (centralizer ({u}:Set G))))
    (hfusion : ∃g:G,g*z*g⁻¹=(v:G))
    (hcard : Nat.card (centralizer ({z}:Set G))=2304) : False := by
  let C := centralizer ({u}:Set G)
  have hp5 : 5≤p := by rcases hp with rfl | rfl <;> decide
  have hn := secondary_component_residual_normalizes hG u hu L K hL hK
  have hf := (secondary_component_faithful_residual_action hG u hu P M z h115 L K hL hK eA a ha hza).1
  have hvK := Theory.PSL2.normal_alternating_four_actor_centralizer_le hp5 L K eK hL eA hn hf hv
  let j : K →* centralizer ({(v:G)}:Set G) :=
    (C.subtype.comp K.subtype).codRestrict _ (fun k=>
      mem_centralizer_singleton_iff.mpr (congrArg C.subtype (hvK k k.property)))
  have hj : Function.Injective j := by
    intro k l h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x:centralizer ({(v:G)}:Set G)=>(x:G)) h
  have hd := card_dvd_of_injective j hj
  have hvc : Nat.card (centralizer ({(v:G)}:Set G))=2304 := by
    obtain ⟨g,hg⟩ := hfusion
    let f := MulAut.conj g
    have he : f z=(v:G) := hg
    rw [←he,←hcard]
    symm
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro b
    change b∈centralizer ({z}:Set G) ↔ f b∈centralizer ({f z}:Set G)
    simp only [mem_centralizer_singleton_iff,←map_mul,f.injective.eq_iff]
  rw [hvc,Nat.card_congr eK.toEquiv] at hd
  have ho : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,Fact.out,(Fact.out : p.Prime).odd_of_ne_two (by omega),by omega,by simp⟩
  rw [GorensteinWalter.psl2_card_formula (ZMod p) ho,Nat.card_zmod] at hd
  rcases hp with rfl | rfl <;> norm_num at hd

open ChapterC ChapterC.Section05.ConjugateSource

/-- The prime rows are impossible for the literal marked secondary residual. -/
theorem MinimalBlockSetup.single_alternating_secondary_prime_false_of_marks
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (eH : d.H≃*BinaryFiveAffine.W) (hm : d.MarkedA5CentralizerPacket eH)
    (hu : orderOf (d.affineInvolution eH)=2)
    (P : Sylow 2 (centralizer ({d.affineInvolution eH}:Set G)))
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({d.affineInvolution eH}:Set G))
      P M (d.affineCentralVector eH))
    (R : Subgroup (centralizer ({d.affineInvolution eH}:Set G)))
    (hgeom : SecondaryResidualGeometry (P:Subgroup (centralizer ({d.affineInvolution eH}:Set G)))
      ((d.affineCentralizerResidual eH).subgroupOf (centralizer ({d.affineInvolution eH}:Set G)))
      R (d.affineCentralVector eH) (d.affineInvolution eH)
      (centralizer ({d.affineInvolution eH}:Set G)).subtype)
    (K : Subgroup (centralizer ({d.affineInvolution eH}:Set G))) [K.Normal]
    (hK : IsComponent (centralizer ({d.affineInvolution eH}:Set G)) K)
    {p : ℕ} [Fact p.Prime] (hp : p=7 ∨ p=17) (eK : K≃*PSL(2,ZMod p))
    (hcard : Nat.card (centralizer ({d.affineCentralVector eH}:Set G))=2304) : False := by
  let u := d.affineInvolution eH
  let z := d.affineCentralVector eH
  let C := centralizer ({u}:Set G)
  let L := (d.affineCentralizerResidual eH).subgroupOf C
  let U := sourceModule (d.block.map d.H.subtype)
  let v := d.affineFirstFixed eH
  have hvfour : v∈d.affineResidualFixedFour eH :=
    (hm.fixed_members v).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hufour : u∈d.affineResidualFixedFour eH :=
    (hm.fixed_members u).mpr (Or.inr (Or.inl rfl))
  let : IsElementaryAbelian 2 U := hA.2.1.elementary.map (d.block.map d.H.subtype).subtype
  have hvC : v∈C := mem_centralizer_singleton_iff.mpr
    ((U.le_centralizer hvfour.1) u hufour.1).symm
  have hvL : (⟨v,hvC⟩:C)∈centralizer (L : Set C) := by
    intro l hl
    apply Subtype.ext
    exact hvfour.2 (l:G) hl
  obtain ⟨a,ha,_,hza⟩ := hgeom.marked
  apply secondary_prime_component_false hG u hu P M z h115 L K hgeom.perfect hK
    hgeom.alternating.some a ha hza hp eK ⟨v,hvC⟩ hvL ?_ hcard
  obtain ⟨g,_,hg⟩ := hm.first_conj
  exact ⟨g,hg⟩

/-- The original maximal centralizer and its marked center discharge the order premise. -/
theorem MinimalBlockSetup.single_alternating_secondary_prime_false_of_centralizer_bot
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hunique : ∀N:Subgroup G, IsMaximalTwoLocal N → (T:Subgroup G)≤N → N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G)⊓centralizer (d.block.map d.H.subtype:Set G)=⊥)
    (eH : d.H≃*BinaryFiveAffine.W) (hm : d.MarkedA5CentralizerPacket eH)
    (hZ :
      let B := M⊓d.block.map d.H.subtype
      let I := (pResidual 2 B).map B.subtype
      let Q := I.pCoreIn 2
      (center Q).map Q.subtype=zpowers (d.affineCentralVector eH))
    (hu : orderOf (d.affineInvolution eH)=2)
    (P : Sylow 2 (centralizer ({d.affineInvolution eH}:Set G)))
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({d.affineInvolution eH}:Set G))
      P M (d.affineCentralVector eH))
    (R : Subgroup (centralizer ({d.affineInvolution eH}:Set G)))
    (hgeom : SecondaryResidualGeometry (P:Subgroup (centralizer ({d.affineInvolution eH}:Set G)))
      ((d.affineCentralizerResidual eH).subgroupOf (centralizer ({d.affineInvolution eH}:Set G)))
      R (d.affineCentralVector eH) (d.affineInvolution eH)
      (centralizer ({d.affineInvolution eH}:Set G)).subtype)
    (K : Subgroup (centralizer ({d.affineInvolution eH}:Set G))) [K.Normal]
    (hK : IsComponent (centralizer ({d.affineInvolution eH}:Set G)) K)
    {p : ℕ} [Fact p.Prime] (hp : p=7 ∨ p=17) (eK : K≃*PSL(2,ZMod p)) : False := by
  have hc := (d.single_alternating_maximal_core_of_centralizer_bot
    hG T hM hTM hunique hST hsingle hA hD).2
  rw [hZ] at hc
  have hz : centralizer ({d.affineCentralVector eH}:Set G)=M := by
    apply (show centralizer ({d.affineCentralVector eH}:Set G)=
      centralizer (zpowers (d.affineCentralVector eH):Set G) from ?_).trans hc.symm
    apply le_antisymm
    · rw [le_centralizer_iff,zpowers_le]
      intro v hv
      exact mem_centralizer_singleton_iff.mp hv
    · exact centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers _))
  apply d.single_alternating_secondary_prime_false_of_marks hG hA eH hm hu P h115 R hgeom K hK hp eK
  rw [hz]
  exact d.single_alternating_maximal_card_of_centralizer_bot hG T hM hTM hunique hST hsingle hA hD

end CFSG.Quasithin.Chapter2
