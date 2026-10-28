module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SourceActions
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.TerminalSupports

/-!
# Original 14.6.24 and the marked terminal witness

The source support theorem excludes both paired-component alternatives and
A₆, identifies the unique residual component as L₃(2), and constructs its
full natural/dual supports and one suitable u. Extend those same section
coordinates to the support normalizer. The existing single-component proofs
then construct the literal parabolic P=C_Mc(u mod Z), its point-stabilizer
action with two-group kernel, the residual R=O²(P), the moving dual
eight-group [B,R], and the fixed factor in the original seed plane.

The selected critical endpoint supplies the noncommuting conjugate and
specified H-match for that same u. Its conjugator x⁻¹ times the endpoint
representative transports every label. The resulting centralizer lies in
the original outside family, which makes I* nonempty. The actual component
action supplies both terminal bounds, and the final theorem applies the
existing terminal-witness consumer with these constructed inputs.

Only MixedSizeInput and original 14.6.18 (hsolv) remain explicit. Their
source discharge belongs to qt-e-suitable-existence and qt-e-14625-source;
this is the conditional source assembly authorized for this component task,
not an unconditional classification theorem. No local support, marking,
coordinate, endpoint, or suitable-vector premise remains.

Source: Aschbacher--Smith, 14.6.24(1--4), printed pp.1038--1041, and the
terminal parabolic argument on printed p.1042.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hunique hmany hcard e hab in
/-- Original 14.6.24 with the actual same-u parabolic, dual eight-group,
fixed-factor coordinates, critical transporter, outside family and bounds.
Every local premise is constructed; the two independent source inputs remain explicit. -/
theorem source_marked_suitable_of_mixed_size
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    ∃ K A B : Subgroup G, ∃ u : G,
      K ≤ Mc ∧ (K.subgroupOf Mc).IsCComponent ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∧
      (solvableResidual Mc).map Mc.subtype = K ∧
      (pResidual 2 Mc).map Mc.subtype = K ∧
      ⁅U,K⁆ = A ⊔ B ∧ A ⊓ B = Z ∧ u ∈ A ∧ ComponentSupports.Suitable h Mc u ∧
      let P := h.kernel (zpowers u)
      let R := (pResidual 2 P).map P.subtype
      Nonempty (SourcePointStabilizerAction P) ∧
      (∃ c ∈ commutatorPreimage U Mc Z,
        ∃ coords : SourceResidualSpanCoordinates (localModule T M) Z R,
          coords.W = ⁅B,R⁆ ∧ coords.a = u*c) ∧
      (∃ i : h.CriticalEndpoint, ∃ x ∈ Mc,
        ∃ crossing : SourceCrossingGeometry (localModule T M) Mc Mc u,
          crossing.A = U ∧ crossing.g = x⁻¹*i.representative ∧
          ∀ D : Subgroup G, D.map (MulAut.conj crossing.g).toMonoidHom =
            (i.conjugate D).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      centralizer ({u} : Set G) ∈ outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M ∧
      (IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)).Nonempty ∧
      primeRank 2 (conjugateSpanBy (localModule T M) R) = 4 ∧ ¬R ≤ M ∧
      4 < (Mc.pCoreIn 2).relIndex (T : Subgroup G) ∧
      4 ≤ Nat.log 2 ((centralizer (Mc.pCoreIn 2 : Set G)).relIndex U) := by
  dsimp only
  obtain ⟨K,hKM,hK,_,hnK,hr,hgen,_,hres,j,A,B,⟨d⟩,⟨d'⟩,hfull,hsep,⟨s,hsB⟩,_,hi,hN,_,
    u,huA,_,_,_,_,_,hu⟩ :=
    ComponentSupports.Modules.Recognition.terminal_exists_full_supports_suitable_of_mixed_size
      hG T hempty hM hunique hmany hcard e hab hsolv size
  obtain ⟨hAU,hBU,hcomm,hpair,f,hf,⟨c⟩,⟨c'⟩⟩ := source_actions_of_component_sections
    hG T hempty hM hunique hmany hcard e hab K hKM hnK hgen j A B d d' hfull hsep s hsB hi hN
  have htwo : (pResidual 2 Mc).map Mc.subtype = K := by rw [←hres]; exact hr
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let C := commutatorPreimage U Mc Z
  have hswap : B.map (MulAut.conj (s:G)).toMonoidHom = A := by
    rw [hsB,map_map]
    have he : (MulAut.conj (s:G)).toMonoidHom.comp (MulAut.conj (s:G)⁻¹).toMonoidHom = MonoidHom.id G := by
      ext a
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,Subgroup.map_id]
  obtain ⟨_,_,b,_,t,ht,coords,hW,ha,_,hrank,hout⟩ := source_residual_geometry_of_paired_supports
    hG T hempty hM hunique hmany hcard e hab A B hAU hBU hsep.le hpair f hf c c' hcomm
    K hr htwo hK j d.normalized s s.property hswap u huA hu
  obtain ⟨_,_,_,hfixed,hcover⟩ := source_fixed_factor_of_pair_commutator
    hG T hempty hM hunique hmany hcard e hab A B hAU hBU hsep.le f hf c c' hcomm
  obtain ⟨_,_,pa,_,_⟩ := source_parabolic_action_of_natural_pair
    hG T hempty hM hunique hmany hcard e hab A B C hsep.le hpair f hf c c' hcover hfixed u huA hu
  obtain ⟨i,x,hx,k,hk,hlabels,crossing,hA,hg,_⟩ := SelectedEndpoint.source_crossing_of_single_component_supports
    hG T hempty hM hunique hmany hcard e hab A B f hf c c' hAU hBU hsep.le hcomm hpair
    K hr hK j d.normalized (s:G)⁻¹ (h.T_le_H ((T:Subgroup G).inv_mem s.property)) hsB.symm u huA hu
  have houtside := source_centralizer_mem_outside_of_geometry
    hG T hempty hM hunique hmany hcard e hab Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
    u hu.1 hu.2.2.2.1 (h.kernel (zpowers u)) le_rfl coords crossing
  let fSL := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp f
  have hfSL : Function.Surjective fSL := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp hf
  obtain ⟨⟨n⟩,⟨dual⟩⟩ := Matrix.PSL3Two.NaturalDualMarking.exists_matrix_pair f c c'
  obtain ⟨hKL,hTK,hKF,honto⟩ := source_component_action_placement
    hG T hempty hM hunique hmany hcard e K A hr hK j d.normalized fSL hfSL
  obtain ⟨hindex,hbound⟩ := source_terminal_bounds_of_natural_dual
    hG T hempty hM hunique hmany hcard e hab (Mc ⊓ normalizer (A:Set G)) K A B
    hKL hTK hKF fSL honto n dual hAU hBU hsep.le
  refine ⟨K,A,B,u,hKM,hK,⟨j⟩,hr,htwo,hfull,hsep,huA,hu,⟨pa⟩,
    ⟨t,ht,coords,hW,ha⟩,⟨i,x,hx,crossing,hA,hg.trans hk,?_⟩,
    houtside,iStar_nonempty ⟨_,houtside⟩,hrank,hout,hindex,hbound⟩
  intro D
  rw [hg]
  exact hlabels D

include hG hempty hM hunique hmany hcard e hab in
/-- Apply the original terminal consumer to the constructed data for the same
suitable u, H=Mc, P=h.kernel(zpowers u), and R=(pResidual 2 P).map P.subtype. -/
theorem source_terminal_witness_of_mixed_size
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  obtain ⟨K,A,B,u,_,_,_,_,_,_,_,_,hu,⟨pa⟩,⟨t,_,coords,_,_⟩,
    ⟨i,x,_,crossing,_,_,_⟩,_,_,_,_,hindex,hbound⟩ :=
    source_marked_suitable_of_mixed_size hG T hempty hM hunique hmany hcard e hab hsolv size
  exact source_terminal_witness_of_geometry
    hG T hempty hM hunique hmany hcard e hab Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
    u hu.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hu.2.2.2.2.2
    hindex hbound (.point pa) coords crossing

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
