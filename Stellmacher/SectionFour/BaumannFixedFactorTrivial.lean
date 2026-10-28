module
public import Stellmacher.SectionFour.BaumannFactorDecomposition
public import Stellmacher.SectionFour.CentralFactorTrivial
public import Stellmacher.SectionFour.BaumannClosureGeneration

/-!
# The fixed module factor vanishes in Stellmacher (4.6)

For the actual Baumann closure L and the original partner module V, the
fixed factor V intersected with the centralizer of L is trivial. This is
the step V₀=1 in Stellmacher (4.6), Journal of Algebra 190 (1997), p.26,
`refs/latex/stellmacher-n-group.tex`.

The fixed factor is normal in the partner since both V and L are normal.
Its ambient image lies in the original Sylow subgroup by the original-V
core containment. It is centralized by L, and L together with that Sylow
generates the partner. The critical-pair central-factor theorem therefore
makes the ambient image trivial; injectivity reflects this to the native
factor. The proof uses no independence or cardinality assertion for the
module decomposition, and retains the literal original V and L throughout.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour
universe u

private theorem fixed_eq_bot
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (P Pstar : Subgroup G) (hpair : (P,Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S)
    (L V : Subgroup Pstar) [L.Normal] [V.Normal]
    (hVS : V.map Pstar.subtype ≤ (S : Subgroup G))
    (hgen : Pstar ≤ L.map Pstar.subtype ⊔ (S : Subgroup G)) :
    V ⊓ Subgroup.centralizer (L : Set Pstar) = ⊥ := by
  let W := V ⊓ Subgroup.centralizer (L : Set Pstar)
  let WA := W.map Pstar.subtype
  have hWA : WA ≤ Pstar := Subgroup.map_subtype_le _
  have hWP : (WA.subgroupOf Pstar).Normal := by
    rw [show WA = W.map Pstar.subtype from rfl, subgroupOf_map_subtype_eq]
    infer_instance
  have hSP : (S : Subgroup G) ≤ Pstar := by
    obtain ⟨T,hT⟩ := hpair.2.1.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hSW : (S : Subgroup G) ≤ Subgroup.normalizer (WA : Set G) :=
    hSP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hWA).mp hWP)
  have hWS : WA ≤ (S : Subgroup G) := (Subgroup.map_mono inf_le_left).trans hVS
  have hLW : L.map Pstar.subtype ≤ Subgroup.centralizer (WA : Set G) := by
    rintro l ⟨l,hl,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro w ⟨w,hw,rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hw.2 l hl).symm
  have hbot := critical_pair_central_factor_eq_bot S P Pstar
    (L.map Pstar.subtype) WA hpair hPC hWS hSW hLW hgen
  exact (Subgroup.map_eq_bot_iff_of_injective W Pstar.subtype_injective).mp hbot

public theorem baumann_fixed_factor_eq_bot
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
    let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
    V ⊓ Subgroup.centralizer (L : Set Pstar) = ⊥ := by
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
  let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  obtain ⟨_, _, _, _, SP, Q, hSP, hQmap, _, hQS, _, _⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hQSambient := Subgroup.map_mono (f := Pstar.subtype) hQS
  rw [hQmap, hSP] at hQSambient
  have hVS : V.map Pstar.subtype ≤ (S : Subgroup G) :=
    (original_v_le_c_core S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl).trans
      hQSambient
  exact fixed_eq_bot S P Pstar hpair hPC L V hVS
    (baumann_closure_sup_sylow S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl).ge

end Stellmacher.SectionFour
