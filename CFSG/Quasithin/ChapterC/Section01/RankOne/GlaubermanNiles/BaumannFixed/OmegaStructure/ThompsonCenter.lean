module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure
public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.GroupTheory.Commutator.NormalGeneration

/-!
# Campbell's Thompson-center replacement identities

Write Q=O₂(H), E=Ω₁(Z(Q)) and F=Ω₁(Z(J(Q))). The sharp fixed-index
bound makes (A∩Q)E a maximum elementary subgroup for every maximum A
of the marked Sylow subgroup. Maximality puts F inside this replacement.
Since E=V·Ω₁(Z(H)), this gives F=V(F∩A), C_A(F)=A∩Q and
[A,F]=[A,V]. The same fixed-summand decomposition holds for every Y
contained in a maximum elementary subgroup. These original-hypothesis
identities feed the literal two-overgroup comparison in CorePlacement.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.4–4.5,
printed p.26; the original local input is Aschbacher–Smith C.1.17.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J]
  {e : B →* H} {k : Type} [Field k] [Finite k] [CharP k 2]

omit [Finite H] in
private theorem omega_le (Q : Subgroup H) : omegaOneCenterAmbient Q ≤ Q :=
  fun _ hx => ((mem_omegaOneCenterAmbient_iff Q _).mp hx).1

omit [Finite H] in
private theorem omega_cent (Q : Subgroup H) :
    omegaOneCenterAmbient Q ≤ centralizer (Q : Set H) :=
  fun _ hx => ((mem_omegaOneCenterAmbient_iff Q _).mp hx).2.2

theorem InLocalClass.omegaCore_replacement_maximal (h : InLocalClass e) (hB : IsBaumannFixed B)
    (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) ∈
      elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  by_cases hAQ : A ≤ pCore 2 H
  · have hEA : omegaOneCenterAmbient (pCore 2 H) ≤ A :=
      maxElementary_contains_elementary_centralizer _ _ _ hA
        ((omega_le _).trans (pCore_isPGroup.le_sylow_of_normal d.sylow))
        ((omega_cent _).trans (centralizer_le hAQ))
    simpa only [inf_eq_left.mpr hAQ, sup_eq_left.mpr hEA] using hA
  · exact maxElementary_inf_sup_mem_of_fixedIndex _ _ _ _
      (pCore_isPGroup.le_sylow_of_normal d.sylow) (omega_le _) (omega_cent _) hA
      (h.omegaFixedIndexBound hB d A hA hAQ)

theorem InLocalClass.campbellF_le_omegaCore_replacement (h : InLocalClass e) (hB : IsBaumannFixed B)
    (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    Campbell.F H ≤ (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) := by
  let R := (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H)
  have hR := InLocalClass.omegaCore_replacement_maximal h hB d A hA
  have hRQ : R ≤ pCore 2 H := sup_le inf_le_right (omega_le _)
  have hmax : R ∈ elementaryAbelianMaxSubgroups (pCore 2 H) :=
    ⟨hRQ,hR.2.1,fun C hC he => hR.2.2 C
      (hC.trans (pCore_isPGroup.le_sylow_of_normal d.sylow)) he⟩
  let : IsElementaryAbelian 2 (Campbell.F H) := omegaOneCenterAmbient_elementaryAbelian _
  apply maxElementary_contains_elementary_centralizer _ _ _ hR
  · exact (omega_le _).trans ((sSup_le fun _ hA => hA.1).trans
      (pCore_isPGroup.le_sylow_of_normal d.sylow))
  · exact (omega_cent _).trans (centralizer_le (le_sSup hmax))

theorem InLocalClass.campbellF_eq_V_sup_inf_maxElementary (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    Campbell.F H = Campbell.V H ⊔ (Campbell.F H ⊓ A) := by
  let : (Campbell.V H).Normal := by rw [h.campbellV_eq_moved hB m]; infer_instance
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hZ : omegaCenter H ≤ A := by
    let : IsElementaryAbelian 2 (omegaCenter H) := by
      rw [← h.omegaCore_inf_center]
      exact IsElementaryAbelian.of_le inf_le_left
    exact maxElementary_contains_elementary_centralizer _ _ _ hA
      (((h.omegaCore_inf_center).symm.le.trans inf_le_left).trans
        ((omega_le _).trans (pCore_isPGroup.le_sylow_of_normal d.sylow)))
      (fun z hz a _ => mem_center_iff.mp
        (((h.omegaCore_inf_center).symm.le hz).2) a)
  have hFA : Campbell.F H ≤ Campbell.V H ⊔ A := by
    apply (InLocalClass.campbellF_le_omegaCore_replacement h hB d A hA).trans
    apply sup_le (inf_le_left.trans le_sup_right)
    rw [h.omegaCore_eq_campbellV_sup_omegaCenter hB m]
    exact sup_le le_sup_left (hZ.trans le_sup_right)
  apply le_antisymm ?_ (sup_le Campbell.V_le_F inf_le_left)
  intro x hx
  obtain ⟨v,hv,a,ha,he⟩ := mem_sup_of_normal_left.mp (hFA hx)
  have haF : a ∈ Campbell.F H := by
    have hh := (Campbell.F H).mul_mem ((Campbell.F H).inv_mem (Campbell.V_le_F hv)) hx
    rw [← he] at hh
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hh
  rw [← he]
  exact mul_mem (mem_sup_left hv) (mem_sup_right ⟨haF,ha⟩)

theorem InLocalClass.campbellF_eq_V_sup_fixed_maxElementary (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    Campbell.F H = Campbell.V H ⊔ (Campbell.F H ⊓ centralizer (A : Set H)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  apply le_antisymm ?_ (sup_le Campbell.V_le_F inf_le_left)
  conv_lhs => rw [InLocalClass.campbellF_eq_V_sup_inf_maxElementary h hB m d A hA]
  exact sup_le_sup le_rfl (inf_le_inf le_rfl (le_centralizer_iff_isMulCommutative.mpr inferInstance))

theorem InLocalClass.maxElementary_commutator_campbellF_eq (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    ⁅A,Campbell.F H⁆ = ⁅A,Campbell.V H⁆ := by
  let : (Campbell.V H).Normal := by rw [h.campbellV_eq_moved hB m]; infer_instance
  apply le_antisymm ?_ (commutator_mono le_rfl Campbell.V_le_F)
  rw [commutator_comm, InLocalClass.campbellF_eq_V_sup_fixed_maxElementary h hB m d A hA]
  apply commutator_le.mpr
  intro x hx a ha
  obtain ⟨v,hv,z,hz,rfl⟩ := mem_sup_of_normal_left.mp hx
  have hza : ⁅z,a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((hz.2 a ha).symm)
  rw [commutatorElement_mul_left_eq_conj_mul,hza,mul_one,mul_inv_cancel,one_mul]
  rw [commutator_comm]
  exact commutator_mem_commutator hv ha

theorem InLocalClass.campbellF_replacement_eq_omegaCore (h : InLocalClass e) (hB : IsBaumannFixed B)
    (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    (A ⊓ pCore 2 H) ⊔ Campbell.F H =
      (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) := by
  exact le_antisymm (sup_le le_sup_left (InLocalClass.campbellF_le_omegaCore_replacement h hB d A hA))
    (sup_le_sup le_rfl Campbell.omegaCore_le_F)

theorem InLocalClass.maxElementary_centralizer_campbellF (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) :
    A ⊓ centralizer (Campbell.F H : Set H) = A ⊓ pCore 2 H := by
  have hSK : (d.sylow : Subgroup H) ⊓ localKernel e = pCore 2 H :=
    d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  have hFK : centralizer (Campbell.F H : Set H) ≤ localKernel e := by
    apply (centralizer_le Campbell.V_le_F).trans
    rw [h.campbellV_eq_moved hB m]
    let : Algebra (ZMod 2) k := ZMod.algebra k 2
    let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
    let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
    obtain ⟨_,_,_,_,_,_,_,he⟩ := h.exists_faithful_natural_action m
    exact he.le
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, hSK ▸ (show x ∈ (d.sylow : Subgroup H) ⊓ localKernel e from
      ⟨hA.1 hx.1,hFK hx.2⟩)⟩
  · apply le_inf inf_le_left
    have hR := InLocalClass.omegaCore_replacement_maximal h hB d A hA
    have hRQ : (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) ≤ pCore 2 H :=
      sup_le inf_le_right (omega_le _)
    have hmax : (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H) ∈
        elementaryAbelianMaxSubgroups (pCore 2 H) :=
      ⟨hRQ,hR.2.1,fun C hC he => hR.2.2 C
        (hC.trans (pCore_isPGroup.le_sylow_of_normal d.sylow)) he⟩
    apply le_centralizer_iff.mpr
    exact (omega_cent _).trans (centralizer_le
      ((le_sup_left : A ⊓ pCore 2 H ≤
        (A ⊓ pCore 2 H) ⊔ omegaOneCenterAmbient (pCore 2 H)).trans (le_sSup hmax)))

omit [Finite H] in
theorem Campbell.F_normal : (Campbell.F H).Normal := by
  rw [normal_iff_map_conj_eq]
  intro g
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ (pCore 2 H))).map
    (MulAut.conj g).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective]
  rw [← elementaryAbelianMaxJ_map_equiv]
  have hQ : (pCore 2 H).map (MulAut.conj g).toMonoidHom = pCore 2 H :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [hQ]
  rfl

theorem InLocalClass.thompson_commutator_campbellF_eq (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) :
    ⁅Campbell.J (d.sylow : Subgroup H),Campbell.F H⁆ =
      ⁅Campbell.J (d.sylow : Subgroup H),Campbell.V H⁆ := by
  let : (Campbell.F H).Normal := Campbell.F_normal
  let : (Campbell.V H).Normal := by rw [h.campbellV_eq_moved hB m]; infer_instance
  rw [commutator_comm, commutator_comm (Campbell.J (d.sylow : Subgroup H))]
  change ⁅Campbell.F H,sSup (elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))⁆ =
    ⁅Campbell.V H,sSup (elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))⁆
  simp_rw [sSup_eq_iSup,commutator_iSup_of_normal_left]
  apply iSup_congr
  intro A
  apply iSup_congr
  intro hA
  rw [commutator_comm,commutator_comm (Campbell.V H)]
  exact InLocalClass.maxElementary_commutator_campbellF_eq h hB m d A hA

theorem InLocalClass.campbellF_submaximal_control (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) (Y A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) (hYA : Y ≤ A) :
    Y ⊓ pCore 2 H ≤ centralizer (Campbell.F H : Set H) ∧
      Campbell.F H = Campbell.V H ⊔ (Campbell.F H ⊓ centralizer (Y : Set H)) := by
  constructor
  · exact (inf_le_inf hYA le_rfl).trans ((InLocalClass.maxElementary_centralizer_campbellF h hB m d A hA).symm.le.trans inf_le_right)
  · apply le_antisymm ?_ (sup_le Campbell.V_le_F inf_le_left)
    conv_lhs => rw [InLocalClass.campbellF_eq_V_sup_fixed_maxElementary h hB m d A hA]
    exact sup_le_sup le_rfl (inf_le_inf le_rfl (centralizer_le hYA))

theorem InLocalClass.campbellF_le_some_maxElementary (h : InLocalClass e) (hB : IsBaumannFixed B)
    (d : Campbell.Embedding J H) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), Campbell.F H ≤ A := by
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (d.sylow : Subgroup H)
  exact ⟨_,InLocalClass.omegaCore_replacement_maximal h hB d A hA,InLocalClass.campbellF_le_omegaCore_replacement h hB d A hA⟩

theorem InLocalClass.sylow_centralizer_campbellF_le_core (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e k) (d : Campbell.Embedding J H) :
    (d.sylow : Subgroup H) ⊓ centralizer (Campbell.F H : Set H) ≤ pCore 2 H := by
  have hSK : (d.sylow : Subgroup H) ⊓ localKernel e = pCore 2 H :=
    d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  rw [← hSK]
  apply inf_le_inf le_rfl
  apply (centralizer_le Campbell.V_le_F).trans
  rw [h.campbellV_eq_moved hB m]
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨_,_,_,_,_,_,_,he⟩ := h.exists_faithful_natural_action m
  exact he.le

end CFSG.Quasithin.ChapterC.GlaubermanNiles
