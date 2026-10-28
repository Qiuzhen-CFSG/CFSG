module
public import Glauberman.MaximumAbelianReplacement
public import Glauberman.SmallMoverBaumann
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# All-abelian Thompson replacement and its enlarged omega layer

Sharp offender indices preserve the maximum order of abelian subgroups when
replacing A by (A intersect Q) V. The full maximum family of Q is consequently
part of that of T. Their central omega subgroups compare in the reverse
direction. Replacement also bounds the commutator of the larger central omega
with the ordinary Thompson subgroup by V, and hence with its normal closure.
These are the all-abelian preparations for the Baumann argument in MS93 (5.1),
printed p.913; no elementary-Thompson convention is substituted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- A sharp offender has a maximum abelian centralizing replacement, even
when it does not cover the entire quotient T/Q. -/
theorem maximum_abelian_replacement_of_sharp {T Q V A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups T) (hQT : Q ≤ T) (hVQ : V ≤ Q)
    (hVc : IsMulCommutative V) (hcentral : V ≤ centralizer (Q : Set G))
    (hsharp : (centralizer (A : Set G)).relIndex V = Q.relIndex A) :
    A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups T ∧
    A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups Q ∧
    Nat.card ↥(A ⊓ Q ⊔ V) = Nat.card A ∧
    thompsonAbelianSubgroups Q ⊆ thompsonAbelianSubgroups T := by
  have hfixed : (V ⊓ centralizer (A : Set G)).relIndex V = Q.relIndex A := by
    rw [inf_relIndex_left,hsharp]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes (A ⊓ Q) V
    ((hcentral.trans (centralizer_le inf_le_right)).trans (centralizer_le_normalizer _))
  have hinter : (A ⊓ Q) ⊓ V = A ⊓ V := by
    ext x
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hVQ h.2⟩,h.2⟩⟩
  rw [hinter] at hprod
  have hVcard := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ V) V bot_le inf_le_right
  have hAcard := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ Q) A bot_le inf_le_left
  simp only [relIndex_bot_left,inf_relIndex_left] at hVcard hAcard
  have hfixed' : (A ⊓ V).relIndex V = Q.relIndex A := by
    rw [←centralizer_intersection_maximum_abelian hA (hVQ.trans hQT),hfixed]
  rw [hfixed'] at hVcard
  have hcard : Nat.card ↥(A ⊓ Q ⊔ V) = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(A ⊓ V)))
    calc
      Nat.card ↥(A ⊓ V) * Nat.card ↥(A ⊓ Q ⊔ V) =
          Nat.card ↥(A ⊓ Q) * Nat.card V := hprod.symm
      _ = Nat.card ↥(A ⊓ V) * Nat.card A := by
        rw [←hVcard,←hAcard]
        ac_rfl
  let _ := hA.2.1
  let _ := hVc
  let _ : IsMulCommutative (A ⊓ Q : Subgroup G) :=
    IsMulCommutative.of_setLike_mul_comm fun _ hx _ hy => setLike_mul_comm hx.1 hy.1
  have hc : IsMulCommutative (A ⊓ Q ⊔ V : Subgroup G) := by
    have hBV := hcentral.trans (centralizer_le (show A ⊓ Q ≤ Q from inf_le_right))
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le (A ⊓ Q).le_centralizer hBV)
    · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hBV) V.le_centralizer)
  have hT : A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups T :=
    ⟨sup_le (inf_le_left.trans hA.1) (hVQ.trans hQT),hc,
      fun B hB hBc => hcard ▸ hA.2.2 B hB hBc⟩
  have hQ : A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups Q :=
    thompsonAbelianSubgroups_mem_of_le hQT hT (sup_le inf_le_right hVQ)
  exact ⟨hT,hQ,hcard,fun B hB =>
    ⟨hB.1.trans hQT,hB.2.1,fun C hC hCc =>
      (hT.2.2 C hC hCc).trans (hB.2.2 _ hQ.1 hQ.2.1)⟩⟩

/-- The ordinary central omega lies in every maximum abelian subgroup. -/
theorem thompson_omega_le_maximum_abelian {T A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups T) : omegaCenterIn (thompsonSubgroup T) ≤ A := by
  apply le_maximum_abelian_of_centralizes hA
  · intro x hx
    exact thompsonSubgroup_le T ((mem_omegaCenterIn_iff _ _).mp hx).1
  · intro x hx
    exact centralizer_le (show A ≤ thompsonSubgroup T from le_sSup hA)
      ((mem_omegaCenterIn_iff _ _).mp hx).2.1

/-- Equal maximum abelian orders reverse the inclusion of central omega
subgroups; the original V is retained as a subgroup of the larger one. -/
theorem thompson_omega_replacement_control
    (T Q V : Subgroup G) [IsElementaryAbelian 2 V]
    (hQT : Q ≤ T) (hVQ : V ≤ Q) (hcentral : V ≤ centralizer (Q : Set G))
    (hsharp : ∀ A ∈ thompsonAbelianSubgroups T,
      (centralizer (A : Set G)).relIndex V = Q.relIndex A) :
    thompsonAbelianSubgroups Q ⊆ thompsonAbelianSubgroups T ∧
    V ≤ omegaCenterIn (thompsonSubgroup Q) ∧
    omegaCenterIn (thompsonSubgroup T) ≤ omegaCenterIn (thompsonSubgroup Q) ∧
    IsElementaryAbelian 2 (omegaCenterIn (thompsonSubgroup T) ⊔ V : Subgroup G) := by
  obtain ⟨A,hA⟩ := thompsonAbelianSubgroups_nonempty T
  have hfamily := (maximum_abelian_replacement_of_sharp hA hQT hVQ
    inferInstance hcentral (hsharp A hA)).2.2.2
  have hJ : thompsonSubgroup Q ≤ thompsonSubgroup T :=
    sSup_le fun B hB => le_sSup (hfamily hB)
  have hV : V ≤ omegaCenterIn (thompsonSubgroup Q) := by
    have hv := smallMover_fixed_le_thompson_omega V Q Q hVQ (thompsonSubgroup_le Q)
    simpa only [inf_eq_left.mpr hcentral] using hv
  have halpha : omegaCenterIn (thompsonSubgroup T) ≤ omegaCenterIn (thompsonSubgroup Q) := by
    obtain ⟨B,hB⟩ := thompsonAbelianSubgroups_nonempty Q
    intro x hx
    obtain ⟨_,hc,h2⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨le_sSup hB (thompson_omega_le_maximum_abelian (hfamily hB) hx),centralizer_le hJ hc,h2⟩
  let : IsElementaryAbelian 2 (omegaCenterIn (thompsonSubgroup Q)) := inferInstance
  exact ⟨hfamily,hV,halpha,IsElementaryAbelian.of_le (sup_le halpha hV)⟩

/-- Sharp replacement bounds the commutator with the ordinary Thompson
subgroup, without replacing it by the elementary Thompson subgroup. -/
theorem thompson_omega_core_commutator_le
    (T Q V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hQT : Q ≤ T) (hVQ : V ≤ Q) (hcentral : V ≤ centralizer (Q : Set G))
    (hsharp : ∀ A ∈ thompsonAbelianSubgroups T,
      (centralizer (A : Set G)).relIndex V = Q.relIndex A) :
    ⁅omegaCenterIn (thompsonSubgroup Q),thompsonSubgroup T⁆ ≤ V := by
  let q := QuotientGroup.mk' V
  have hcomm (A : Subgroup G) (hA : A ∈ thompsonAbelianSubgroups T) :
      ⁅omegaCenterIn (thompsonSubgroup Q),A⁆ ≤ V := by
    have hr := maximum_abelian_replacement_of_sharp hA hQT hVQ inferInstance hcentral (hsharp A hA)
    have hh := map_mono (f := q) (thompson_omega_le_maximum_abelian hr.2.1)
    rw [Subgroup.map_sup,show V.map q = ⊥ from
      (Subgroup.map_eq_bot_iff V).mpr (by simp [q]),sup_bot_eq] at hh
    let : IsMulCommutative A := hA.2.1
    let : IsMulCommutative (A.map q) := map_isMulCommutative A q
    have hc : (omegaCenterIn (thompsonSubgroup Q)).map q ≤
        centralizer (A.map q : Set (G ⧸ V)) :=
      hh.trans ((map_mono inf_le_left).trans (A.map q).le_centralizer)
    have hz := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hz
    exact hz
  rw [←QuotientGroup.ker_mk' V,←Subgroup.map_eq_bot_iff,commutator_comm,map_commutator,
    commutator_eq_bot_iff_le_centralizer,map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  have hh := hcomm A hA
  rw [←QuotientGroup.ker_mk' V,←Subgroup.map_eq_bot_iff,commutator_comm,map_commutator,
    commutator_eq_bot_iff_le_centralizer] at hh
  exact map_le_iff_le_comap.mp hh

/-- The enlarged central omega is normalized by the Thompson normal closure
and by T. The commutator estimate retains the whole original V. -/
theorem thompson_omega_enlargement_normalized
    (T Q V : Subgroup G) [Q.Normal] [V.Normal] [IsElementaryAbelian 2 V]
    (hQT : Q ≤ T) (hVQ : V ≤ Q) (hcentral : V ≤ centralizer (Q : Set G))
    (hsharp : ∀ A ∈ thompsonAbelianSubgroups T,
      (centralizer (A : Set G)).relIndex V = Q.relIndex A) :
    ⁅omegaCenterIn (thompsonSubgroup T) ⊔ V,
      normalClosure (thompsonSubgroup T : Set G)⁆ ≤ V ∧
    normalClosure (thompsonSubgroup T : Set G) ⊔ T ≤
      normalizer ((omegaCenterIn (thompsonSubgroup T) ⊔ V : Subgroup G) : Set G) := by
  have hh := thompson_omega_replacement_control T Q V hQT hVQ hcentral hsharp
  have hnorm (P : Subgroup G) : normalizer (P : Set G) ≤
      normalizer (omegaCenterIn (thompsonSubgroup P) : Set G) :=
    (normalizer_le_normalizer_of_thompsonSubgroup P).trans
      (normalizer_le_normalizer_omegaCenterIn _)
  let : (omegaCenterIn (thompsonSubgroup Q)).Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique (le_normalizer_of_normal.trans (hnorm Q))
  have hc := commutator_normalClosure_le_of_normal _ _ V
    (thompson_omega_core_commutator_le T Q V hQT hVQ hcentral hsharp)
  have hw : ⁅omegaCenterIn (thompsonSubgroup T) ⊔ V,
      normalClosure (thompsonSubgroup T : Set G)⁆ ≤ V :=
    (commutator_mono (sup_le hh.2.2.1 hh.2.1) le_rfl).trans hc
  refine ⟨hw,sup_le ?_ ?_⟩
  · exact le_normalizer_iff_commutator_le_left.mpr (hw.trans le_sup_right)
  · exact (le_inf (T.le_normalizer.trans (hnorm T))
      (show T ≤ normalizer (V : Set G) from le_normalizer_of_normal)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- A nontrivial Thompson image in a simple quotient makes the enlarged
central omega ambient-normal. The full quotient kernel remains inside T. -/
theorem thompson_omega_enlargement_normal_of_simple_image
    {D : Type*} [Group D] [IsSimpleGroup D]
    (T V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* D) (hq : Function.Surjective q) (hkT : q.ker ≤ T)
    (hVk : V ≤ q.ker) (hcentral : V ≤ centralizer (q.ker : Set G))
    (hJ : ¬ thompsonSubgroup T ≤ q.ker)
    (hsharp : ∀ A ∈ thompsonAbelianSubgroups T,
      (centralizer (A : Set G)).relIndex V = q.ker.relIndex A) :
    (omegaCenterIn (thompsonSubgroup T) ⊔ V : Subgroup G).Normal := by
  let N := normalClosure (thompsonSubgroup T : Set G)
  let : (N.map q).Normal := Normal.map inferInstance q hq
  have hN : N.map q = ⊤ := by
    rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with hz | ht
    · exact False.elim (hJ (le_normalClosure.trans ((Subgroup.map_eq_bot_iff N).mp hz)))
    · exact ht
  have hgen : N ⊔ q.ker = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hN
    rwa [comap_map_eq,comap_top] at hh
  have hn := (thompson_omega_enlargement_normalized T q.ker V hkT hVk hcentral hsharp).2
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  exact (sup_le_sup_left hkT N).trans hn

/-- With a two-group kernel, the residual moves the enlarged omega layer
only inside the full original elementary layer. -/
theorem thompson_omega_residual_control
    {D : Type*} [Group D] [IsSimpleGroup D]
    (T V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hkT : q.ker ≤ T) (hVk : V ≤ q.ker) (hcentral : V ≤ centralizer (q.ker : Set G))
    (hJ : ¬ thompsonSubgroup T ≤ q.ker)
    (hsharp : ∀ A ∈ thompsonAbelianSubgroups T,
      (centralizer (A : Set G)).relIndex V = q.ker.relIndex A) :
    ⁅omegaCenterIn (thompsonSubgroup q.ker),pResidual 2 G⁆ ≤ V ∧
    ⁅omegaCenterIn (thompsonSubgroup T) ⊔ V,pResidual 2 G⁆ ≤ V := by
  let N := normalClosure (thompsonSubgroup T : Set G)
  let : (N.map q).Normal := Normal.map inferInstance q hq
  have hN : N.map q = ⊤ := by
    rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with hz | ht
    · exact False.elim (hJ (le_normalClosure.trans ((Subgroup.map_eq_bot_iff N).mp hz)))
    · exact ht
  have hgen : N ⊔ q.ker = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hN
    rwa [comap_map_eq,comap_top] at hh
  have hres : pResidual 2 G ≤ N :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N q.ker hk hgen⟩
  let : (omegaCenterIn (thompsonSubgroup q.ker)).Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique (le_normalizer_of_normal.trans
      ((normalizer_le_normalizer_of_thompsonSubgroup q.ker).trans
        (normalizer_le_normalizer_omegaCenterIn _)))
  have hkernel := (commutator_mono le_rfl hres).trans
    (commutator_normalClosure_le_of_normal _ _ V
      (thompson_omega_core_commutator_le T q.ker V hkT hVk hcentral hsharp))
  exact ⟨hkernel,(commutator_mono le_rfl hres).trans
    (thompson_omega_enlargement_normalized T q.ker V hkT hVk hcentral hsharp).1⟩

end Glauberman
