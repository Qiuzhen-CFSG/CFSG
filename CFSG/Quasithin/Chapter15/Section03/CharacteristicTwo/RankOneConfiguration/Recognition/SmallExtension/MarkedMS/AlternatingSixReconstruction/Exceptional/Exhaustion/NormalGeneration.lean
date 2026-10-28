module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Quotient
public import Theory.GroupTheory.PCoreOddIndex

/-!
# Normal generation with the cubic covering kernel retained

In M = LR put K = L, Q = O₂(M), and E equal to the original extension
kernel. The quasisimple component of M/Q proves that every normal subgroup
above Q either lies in E or contains K. Since E/Q has order three, an
escaping two-subgroup rules out the former case. Applying this to the
centralizer of an abelian section of Q detects the entire commutator [Q,K]
from the action of that two-subgroup.

This is the normal-generation step used in the first paragraph of MS93
(3.6), printed p.870. It does not replace E by Q or require the original
radical to be Sylow. The graph critical-endpoint application is in Critical.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M

/-- A normal subgroup containing Q either lies in the retained odd kernel
or contains the entire original component. -/
theorem normal_over_core_dichotomy (h : SmallMSPair κ L R) (e : CentralMarking L)
    (N : Subgroup M) [N.Normal] (hQN : Q ≤ N) :
    N ≤ extensionKernel h ∨ K ≤ N := by
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  let q := QuotientGroup.mk' Q
  let C := componentImage L R
  let : C.Normal := (inferInstance : (K).Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv
    (cComponentTwoCoreQuotientEquiv h.component)
  let : (N.map q).Normal := (inferInstance : N.Normal).map q
    (QuotientGroup.mk'_surjective _)
  have hC : IsComponent (M ⧸ Q) C :=
    ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  rcases hC.normal_dichotomy (N.map q) with hn | hc
  · right
    have hh := map_le_iff_le_comap.mp hn
    rwa [comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hQN] at hh
  · left
    rw [commutator_comm] at hc
    rw [extensionKernel_eq_comap_centralizer h e]
    exact map_le_iff_le_comap.mp (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The odd quotient E/Q cannot contain the image of an escaping two-group. -/
theorem two_subgroup_le_core_of_le_extensionKernel
    (h : SmallMSPair κ L R) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (A : Subgroup M) (hA : IsPGroup 2 A) (hAE : A ≤ extensionKernel h) : A ≤ Q := by
  apply hA.le_pCore_of_le_oddIndexOverCore
    (show Q ≤ extensionKernel h from le_sup_right) _ hAE
  change ¬ 2 ∣ ((pCore 2 M).comap (extensionKernel h).subtype).index
  rw [← pCore_subnormal_eq_comap 2 (inferInstance : (extensionKernel h).Normal).isSubnormal,
    extensionKernel_core_index h hz]
  decide

/-- The normal closure of an escaping two-subgroup contains the component
modulo Q. The source odd central kernel is retained throughout. -/
theorem component_le_normal_of_two_subgroup
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (N A : Subgroup M) [N.Normal] (hQN : Q ≤ N)
    (hA : IsPGroup 2 A) (hAQ : ¬ A ≤ Q) (hAN : A ≤ N) : K ≤ N := by
  exact (normal_over_core_dichotomy h e N hQN).resolve_left fun hn =>
    hAQ (two_subgroup_le_core_of_le_extensionKernel h hz A hA (hAN.trans hn))

/-- Any escaping two-subgroup detects residual action on an abelian section
of Q, including its Frattini section. -/
theorem core_le_of_two_subgroup_commutator_le
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (N A : Subgroup M) [N.Normal] (hQQ : ⁅Q,Q⁆ ≤ N)
    (hA : IsPGroup 2 A) (hAQ : ¬ A ≤ Q) (hcomm : ⁅Q,A⁆ ≤ N) : ⁅Q,K⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let C := (centralizer ((Q).map q : Set (M ⧸ N))).comap q
  let : ((Q).map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hc (B : Subgroup M) : B ≤ C ↔ ⁅Q,B⁆ ≤ N := by
    change B ≤ (centralizer ((Q).map q : Set (M ⧸ N))).comap q ↔ _
    rw [← map_le_iff_le_comap, ← le_centralizer_iff,
      ← commutator_eq_bot_iff_le_centralizer, ← map_commutator,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact (hc K).mp (component_le_normal_of_two_subgroup h e hz C A
    ((hc Q).mpr hQQ) hA hAQ ((hc A).mpr hcomm))

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
