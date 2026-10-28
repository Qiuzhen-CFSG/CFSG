module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionBaer
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# A characteristic elementary envelope in the order-four partner branch

The core Q acts on E through at most the exchange of its two marked
four-groups. A maximum elementary subgroup of Q cannot exchange them:
its centralizer on E has order at most four, whereas its action index
is at most two. The elementary replacement by E would be larger.
Thus J(Q) centralizes E. The characteristic group Ω₁Z(J(Q)) contains E
and its entire C_G(U)-span, making that span elementary.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem core_maxJ_centralizes_diagonal_pair
    (T S Q E U Z₁ Z₂ : Subgroup G) [IsElementaryAbelian 2 E]
    (hQT : Q≤T) (hEQ : E≤Q) (hi : S.relIndex T=2)
    (hE : Nat.card E=16) (hZ₁ : Nat.card Z₁=4)
    (hZ₁E : Z₁≤E)
    (hgen : U⊔Z₁=E) (hdU : Disjoint U Z₁) (hdZ : Disjoint Z₁ Z₂)
    (hQC : Q≤centralizer (U : Set G)) (hmove : ⁅Q,E⁆≤U)
    (hstable : S≤normalizer (Z₁ : Set G))
    (hexchange : ∀q∈Q, q∉S → Z₁.map (MulAut.conj q).toMonoidHom=Z₂) :
    elementaryAbelianMaxJ Q≤centralizer (E : Set G) := by
  have hSC : Q⊓S≤centralizer (E : Set G) := by
    intro q hq
    have hqZ : q∈centralizer (Z₁ : Set G) := by
      intro z hz
      have hcomm : ⁅q,z⁆∈U⊓Z₁ := ⟨hmove (commutator_mem_commutator hq.1 (hZ₁E hz)),
        Z₁.mul_mem ((mem_normalizer_iff.mp (hstable hq.2) z).mp hz) (Z₁.inv_mem hz)⟩
      exact (commutatorElement_eq_one_iff_mul_comm.mp
        (mem_bot.mp (disjoint_iff.mp hdU ▸ hcomm))).symm
    have hh : U⊔Z₁≤centralizer ({q} : Set G) := sup_le
      (by intro u hu; simpa only [mem_centralizer_singleton_iff] using hQC hq.1 u hu)
      (by intro z hz; simpa only [mem_centralizer_singleton_iff] using hqZ z hz)
    intro e he
    exact mem_centralizer_singleton_iff.mp (hh (hgen.symm ▸ he))
  apply sSup_le
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1
  by_contra hnot
  obtain ⟨a,ha,hane⟩ := Set.not_subset.mp hnot
  have haS : a∉S := fun hh => hane (hSC ⟨hA.1 ha,hh⟩)
  have hex := hexchange a (hA.1 ha) haS
  let C := A⊓centralizer (E : Set G)
  let I := E⊓C
  let D := A⊓S
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have hDC : D≤C := by
    intro d hd
    exact ⟨hd.1,hSC ⟨hA.1 hd.1,hd.2⟩⟩
  have hcardA : Nat.card A≤2*Nat.card C := by
    have hind : S.relIndex A≤2 := by
      simpa only [hi] using relIndex_le_of_le_right (H:=S) (hA.1.trans hQT)
        (show S.relIndex T≠0 from by rw [hi]; decide)
    have he : Nat.card D*S.relIndex A=Nat.card A := by
      simpa only [D,relIndex_bot_left,inf_relIndex_left] using
        relIndex_mul_relIndex (⊥ : Subgroup G) D A bot_le inf_le_left
    have hcd := card_le_of_le hDC
    nlinarith
  have hIZ : Disjoint I Z₁ := by
    apply disjoint_def.mpr
    intro x hx hxZ
    have hax : a*x*a⁻¹=x := by
      have hc : a*x=x*a := congrArg Subtype.val
        (mul_comm (⟨a,ha⟩ : A) ⟨x,hx.2.1⟩)
      rw [hc,mul_inv_cancel_right]
    have hxZ₂ : x∈Z₂ := hax ▸ (hex ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hxZ)
    exact disjoint_def.mp hdZ hxZ hxZ₂
  have hIZcomm : Z₁≤centralizer (I : Set G) := by
    intro z hz i hi
    exact congrArg Subtype.val (mul_comm (⟨i,hi.1⟩ : E) ⟨z,hZ₁E hz⟩)
  have hcardI : Nat.card I≤4 := by
    have hp := card_sup_eq_mul_of_normalizes_of_disjoint I Z₁
      (hIZcomm.trans (Subgroup.centralizer_le_normalizer _)) hIZ
    have hb := card_le_of_le (sup_le (show I≤E from inf_le_left) hZ₁E)
    rw [hp,hZ₁,hE] at hb
    omega
  have hCE : C≤centralizer (E : Set G) := inf_le_right
  let : IsElementaryAbelian 2 (E⊔C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hCE
  have hmax := hA.2.2 (E⊔C) (sup_le hEQ (inf_le_left.trans hA.1)) inferInstance
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes E C
    (hCE.trans (Subgroup.centralizer_le_normalizer _))
  change Nat.card E*Nat.card C=Nat.card I*Nat.card (E⊔C : Subgroup G) at hprod
  rw [hE] at hprod
  have hpos : 0<Nat.card C := Nat.card_pos
  nlinarith

omit [Finite G] in
private theorem kernel_envelope_normalizer (Q : Subgroup G) :
    normalizer (Q : Set G)≤normalizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hQg : Q.map (MulAut.conj g).toMonoidHom=Q := mem_normalizer_iff_map_conj_eq.mp hg
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ Q)).map (MulAut.conj g).toMonoidHom=_
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    ←elementaryAbelianMaxJ_map_equiv,hQg]

/-- In the actual order-four partner branch, the original fixed subgroup
and its entire partner-kernel span lie in the characteristic elementary
Thompson-center envelope of the actual partner two-core. -/
theorem PreparedChosenModule.decomposable_five_partner_four_fixed_envelope
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let C := centralizer (Uc : Set G)
      let Q := C.pCoreIn 2
      let F := conjugateSpanBy E C
      let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
      elementaryAbelianMaxJ Q≤centralizer (E : Set G) ∧ E≤A ∧ F≤A ∧
        IsElementaryAbelian 2 F ∧ Mc≤normalizer (A : Set G) ∧ Mc≤normalizer (F : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy E C
  let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let S := (T : Subgroup G)⊓normalizer (plane V (c.ambientFactor d s.first).space : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨hCMc,hcore,hQT,_,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hEQ : E≤Q := (h.decomposable_five_partner_four_fixed_le_twoCore
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).trans_eq hcore.symm
  obtain ⟨hd₁,_,hgen₁,_,hmove⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hJE : elementaryAbelianMaxJ Q≤centralizer (E : Set G) := by
    apply core_maxJ_centralizes_diagonal_pair (T : Subgroup G) S Q E Uc Z₁ Z₂
      hQT hEQ s.stabilizer_index s.fixed_card (s.thompson_card s.first)
      inf_le_right hgen₁ hd₁
      (disjoint_iff.mpr s.thompson_disjoint) (pCoreIn_le 2 _) hmove
      (s.thompson_normalized.trans inf_le_left)
    intro q hq hqS
    exact (s.thompson_exchanges q (hQT hq) (fun hh => hqS ⟨hQT hq,hh⟩)).1
  have hEA : E≤A := elementary_centralizer_maxJ_le_omegaCenter Q E hEQ
    (le_centralizer_iff.mp hJE)
  have hMcQ : Mc≤normalizer (Q : Set G) := by
    change Mc≤normalizer (C.pCoreIn 2 : Set G)
    rw [hcore]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hMcA : Mc≤normalizer (A : Set G) := hMcQ.trans (kernel_envelope_normalizer Q)
  have hFA : F≤A := conjugateSpanBy_le hEA (hCMc.trans hMcA)
  let : IsElementaryAbelian 2 A := omegaOneCenterAmbient_elementaryAbelian _
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hIE : M⊓Mc≤normalizer (E : Set G) := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.1
  have hMcCN : Mc≤normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc).trans
      (normalizer_le_normalizer_centralizer _)
  have hIF : M⊓Mc≤normalizer (F : Set G) :=
    normalizes_conjugateSpanBy E C (M⊓Mc) hIE (inf_le_right.trans hMcCN)
  have hMcF : Mc≤normalizer (F : Set G) := by
    intro m hm
    obtain ⟨a,ha,c,hc,rfl⟩ :=
      source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc ⟨hMcC.1,hTMc⟩ m hm
    exact (normalizer (F : Set G)).mul_mem (hIF ⟨ha.2,ha.1⟩)
      ((le_normalizer_conjugateSpanBy E C) hc.2)
  exact ⟨hJE,hEA,hFA,IsElementaryAbelian.of_le hFA,hMcA,hMcF⟩

end CFSG.Quasithin.Chapter15.Section01
