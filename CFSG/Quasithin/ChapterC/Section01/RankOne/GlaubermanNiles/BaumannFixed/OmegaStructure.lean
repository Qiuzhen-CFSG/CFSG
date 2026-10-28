module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.Generators

/-!
# Campbell's omega-core decomposition from C.1.17

Two conjugate maximum elementary subgroups, together with O₂(H), generate
H. Each fixes an index-q subgroup of E=Ω₁(Z(O₂(H))), so |E:C_E(H)|≤q².
The original moved quotient has order q² and its fixed subgroup contains
C_moved(H); hence equality holds and E=moved·C_E(H). This works also over F₂.
Consequently Campbell's V=[H,E] is exactly the marked moved subgroup,
E=V·Ω₁(Z(H)), the action kernel centralizes E, and the originally marked
fixed subgroup is precisely C_V(H). The last identity retains the exact
natural quotient and the commutator is full.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.1(ii),(iii),(vi),
printed pp.24–25, from the original Aschbacher–Smith C.1.17 hypotheses.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}

omit [Finite H] in
theorem central_index_le_square_of_two_conjugate_generators (E Q A : Subgroup H) [E.Normal]
    (hEQ : E ≤ centralizer (Q : Set H)) (g : H)
    (hgen : Q ⊔ A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤) :
    (center H).relIndex E ≤ ((centralizer (A : Set H)).relIndex E)^2 := by
  let c := (MulAut.conj g).toMonoidHom
  have hCmap : (centralizer (A : Set H)).map c = centralizer (A.map c : Set H) := by
    apply le_antisymm (map_centralizer_le_centralizer_image _ _) ?_
    intro x hx
    refine ⟨(MulAut.conj g).symm x,?_,(MulAut.conj g).apply_symm_apply x⟩
    intro y hy
    apply (MulAut.conj g).injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using hx ((MulAut.conj g) y) (mem_map_of_mem c hy)
  have hEmap : E.map c = E :=
    mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (E : Set H) from
      le_normalizer_of_normal (mem_top g))
  have hidx : (centralizer (A.map c : Set H)).relIndex E = (centralizer (A : Set H)).relIndex E := by
    calc
      _ = ((centralizer (A : Set H)).map c).relIndex (E.map c) := by rw [hCmap,hEmap]
      _ = _ := relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have hfix : (center H).subgroupOf E =
      (centralizer (A : Set H) ⊓ centralizer (A.map c : Set H)).subgroupOf E := by
    ext x
    constructor
    · intro hx
      exact ⟨fun a _ => mem_center_iff.mp hx a,fun a _ => mem_center_iff.mp hx a⟩
    · rintro ⟨hA,hAg⟩
      apply mem_center_iff.mpr
      intro z
      have hh : Q ⊔ A ⊔ A.map c ≤ centralizer ({(x : H)} : Set H) := by
        apply sup_le (sup_le ?_ ?_) ?_
        · intro a ha
          rw [mem_centralizer_singleton_iff]
          exact hEQ x.property a ha
        · intro a ha
          rw [mem_centralizer_singleton_iff]
          exact hA a ha
        · intro a ha
          rw [mem_centralizer_singleton_iff]
          exact hAg a ha
      have hz := hh (hgen ▸ mem_top z)
      exact mem_centralizer_singleton_iff.mp hz
  have heq : (center H).relIndex E =
      (centralizer (A : Set H) ⊓ centralizer (A.map c : Set H)).relIndex E := congrArg Subgroup.index hfix
  rw [heq]
  exact relIndex_inf_le.trans_eq (by rw [hidx,pow_two])
end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative commutatorElement
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
  {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite B] in
theorem InLocalClass.omegaCore_inf_center (h : InLocalClass e) :
    omegaOneCenterAmbient (pCore 2 H) ⊓ center H = omegaCenter H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    have hp := ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.1
    let z : center H := ⟨x,hc⟩
    have hz : z ∈ omega₁ (center H) (p := 2) := by
      apply Subgroup.subset_closure
      change z^2=1
      exact Subtype.ext hp
    exact ⟨z,hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    have hQ : (z : H) ∈ pCore 2 H := h.core_selfCentralizing
      (fun y _ => mem_center_iff.mp z.property y)
    let : IsElementaryAbelian 2 (omega₁ (center H) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative (center H)
    have hp : (z : H)^2=1 := congrArg Subtype.val
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)
    exact ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hQ,hp,fun y _ => mem_center_iff.mp z.property y⟩,z.property⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J]
  {e : B →* H} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem InLocalClass.omegaCore_center_index_le (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) :
    (center H).relIndex (omegaOneCenterAmbient (pCore 2 H)) ≤ Nat.card F ^ 2 := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨A,g,_,_,hgen,hidx⟩ := InLocalClass.exists_two_maxElementary_generators h hB m d hS
  let : (omegaOneCenterAmbient (pCore 2 H)).Normal := Campbell.omegaCore_normal
  have hC : omegaOneCenterAmbient (pCore 2 H) ≤ centralizer (pCore 2 H : Set H) :=
    fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
  exact (central_index_le_square_of_two_conjugate_generators _ _ _ hC g hgen).trans_eq (by rw [hidx])

theorem InLocalClass.omegaCore_eq_moved_sup_center (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) :
    omegaOneCenterAmbient (pCore 2 H) = moved e ⊔
      (omegaOneCenterAmbient (pCore 2 H) ⊓ center H) := by
  let E := omegaOneCenterAmbient (pCore 2 H)
  let C := E ⊓ center H
  let D := moved e ⊔ C
  let : E.Normal := Campbell.omegaCore_normal
  let : C.Normal := inferInstanceAs (E ⊓ center H).Normal
  have hME : moved e ≤ E := h.moved_le_coreOmegaCenter
  have hDE : D ≤ E := sup_le hME inf_le_left
  have hfix : (center H).subgroupOf (moved e) ≤ movedFixed e := by
    intro x hx a ha
    exact mem_center_iff.mp hx a
  have hM : Nat.card F^2 ≤ (center H).relIndex (moved e) := by
    rw [← m.module_card e]
    exact index_antitone hfix
  have hCM : Nat.card F^2 ≤ C.relIndex (moved e) := by
    have he : C.subgroupOf (moved e) = (center H).subgroupOf (moved e) := by
      ext x
      exact and_iff_right (hME x.property)
    change Nat.card F^2 ≤ (C.subgroupOf (moved e)).index
    rw [he]
    exact hM
  have hCD : Nat.card F^2 ≤ C.relIndex D := by
    change Nat.card F^2 ≤ C.relIndex (moved e ⊔ C)
    rw [relIndex_sup_right]
    exact hCM
  have hCE : C.relIndex E ≤ Nat.card F^2 := by
    change (E ⊓ center H).relIndex E ≤ _
    rw [inf_relIndex_left]
    exact InLocalClass.omegaCore_center_index_le h hB m
  have hm := relIndex_mul_relIndex C D E (show C ≤ D from le_sup_right) hDE
  have hle : D.relIndex E ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left (c := C.relIndex D) ?_ (Nat.pos_of_ne_zero index_ne_zero_of_finite)
    rw [mul_one,hm]
    exact hCE.trans hCD
  have he : D.relIndex E = 1 := by
    have hn : D.relIndex E ≠ 0 := index_ne_zero_of_finite
    omega
  exact le_antisymm (relIndex_eq_one.mp he) hDE
end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative commutatorElement
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem InLocalClass.campbellV_eq_moved (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) : Campbell.V H = moved e := by
  apply le_antisymm ?_ ?_
  · change ⁅(⊤ : Subgroup H),omegaOneCenterAmbient (pCore 2 H)⁆ ≤ moved e
    rw [commutator_comm,InLocalClass.omegaCore_eq_moved_sup_center h hB m]
    apply commutator_le.mpr
    intro x hx g hg
    obtain ⟨y,hy,z,hz,rfl⟩ := mem_sup_of_normal_left.mp hx
    have hzg : ⁅z,g⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      ((mem_center_iff.mp hz.2) g).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzg,mul_one,mul_inv_cancel,one_mul]
    exact commutator_le_left (moved e) ⊤ (commutator_mem_commutator hy hg)
  · change ⁅localV e,actorLift e⁆ ≤ ⁅(⊤ : Subgroup H),omegaOneCenterAmbient (pCore 2 H)⁆
    rw [commutator_comm (⊤ : Subgroup H)]
    exact commutator_mono h.localV_le_coreOmegaCenter le_top

theorem InLocalClass.omegaCore_eq_campbellV_sup_omegaCenter (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) :
    omegaOneCenterAmbient (pCore 2 H) = Campbell.V H ⊔ omegaCenter H := by
  rw [InLocalClass.omegaCore_eq_moved_sup_center h hB m,InLocalClass.omegaCore_inf_center h,InLocalClass.campbellV_eq_moved h hB m]

theorem InLocalClass.kernel_centralizes_omegaCore (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) :
    localKernel e ≤ centralizer (omegaOneCenterAmbient (pCore 2 H) : Set H) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨_,_,_,_,_,_,_,hker⟩ := h.exists_faithful_natural_action m
  apply Subgroup.le_centralizer_iff.mpr
  rw [InLocalClass.omegaCore_eq_moved_sup_center h hB m]
  apply sup_le
  · rw [← hker]
    intro x hx k hk
    exact (hk x hx).symm
  · intro x hx k _
    exact mem_center_iff.mp hx.2 k

theorem InLocalClass.movedFixed_eq_center (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) : movedFixed e = (center H).subgroupOf (moved e) := by
  have hfix : (center H).subgroupOf (moved e) ≤ movedFixed e := by
    intro x hx a ha
    exact mem_center_iff.mp hx a
  apply le_antisymm ?_ hfix
  by_contra hn
  have hl := index_strictAnti (lt_of_le_not_ge hfix hn)
  have hu : (center H).relIndex (moved e) ≤ Nat.card F ^2 :=
    (relIndex_le_of_le_right h.moved_le_coreOmegaCenter index_ne_zero_of_finite).trans
      (InLocalClass.omegaCore_center_index_le h hB m)
  change Nat.card (MovedModule e) < (center H).relIndex (moved e) at hl
  rw [m.module_card e] at hl
  exact hl.not_ge hu

theorem InLocalClass.moved_commutator_eq_self (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) : ⁅moved e,(⊤ : Subgroup H)⁆ = moved e := by
  apply le_antisymm (commutator_le_left _ _) ?_
  have hc : localV e ≤ moved e ⊔ (center H) :=
    h.localV_le_coreOmegaCenter.trans ((InLocalClass.omegaCore_eq_moved_sup_center h hB m).le.trans
      (sup_le_sup le_rfl inf_le_right))
  change ⁅localV e,actorLift e⁆ ≤ ⁅moved e,(⊤ : Subgroup H)⁆
  apply commutator_le.mpr
  intro x hx g hg
  obtain ⟨y,hy,z,hz,rfl⟩ := mem_sup_of_normal_left.mp (hc hx)
  have hzg : ⁅z,g⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((mem_center_iff.mp hz) g).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzg,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hy (mem_top g)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
