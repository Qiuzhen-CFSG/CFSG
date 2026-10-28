module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NaturalCenter
public import Theory.Representation.SL3.PointLocalFixed
public import Theory.Representation.SL3.NaturalParabolicFixed

/-!
# Identifying the whole component-fixed factor of an MS core

A fixed element in a marked section maps to a fixed vector in its model.
Natural SL₃ modules and their duals have no fixed vectors, so the three
upper sections in C.1.34(4) lower every element of C_Q(K) successively to
C_Q(Φ(Q)), Φ(Q), and Z(Q). The checked natural moved-center splitting
therefore splits the whole center over the actual C_Q(K), including at
field four. The third row's two whole sections instead give C_Q(K)=1.

If C_Q(K)=1 is known independently, the natural moved center is already
the whole center, without upper-section hypotheses. The original nonblock
consumer supplies that fixed-point condition from its line-parabolic
configuration. These are conditional section reductions: whole-section
recognition, the fourth-row fixed-factor order and the remaining radical
inequalities are still required. No ambient centrality is inferred.

Source: Aschbacher--Smith C.1.34(3)--(4), pp.136--137, and original
4.3.8--10, pp.616--617. Applications retain the literal original groups
in NonblockMSClassification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.FixedCore
open Chapter1.RadicalExclusions.ModelReduction.FullSieve SourceInterface
variable {G : Type*} [Group G] {K R : Subgroup G}
variable {F : Type} [Field F]

private theorem fixed_le_lower {B W : Type*} [Group B] [AddCommGroup W] [Module F W]
    {D E : Subgroup G} {a : K →* B} {ρ : Representation F B W}
    (hm : HasSectionModel K D E a ρ) (ha : Function.Surjective a)
    (hfix : ∀ w : W, (∀ b, ρ b w = w) → w = 0) :
    D ⊓ centralizer (K : Set G) ≤ E := by
  obtain ⟨_,_,_,hN,e,he⟩ := hm
  let := hN
  rintro x ⟨hx,hc⟩
  let d : D := ⟨x,hx⟩
  have hz : (e (QuotientGroup.mk' (E.subgroupOf D) d)).toAdd = 0 := by
    apply hfix
    intro b
    obtain ⟨k,rfl⟩ := ha b
    apply (he k d d ?_).symm
    change x = (k : G) * x * (k : G)⁻¹
    rw [hc k k.property,mul_inv_cancel_right]
  have hz' : QuotientGroup.mk' (E.subgroupOf D) d = 1 :=
    e.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)
  exact (QuotientGroup.eq_one_iff d).mp hz'

private theorem natural_fixed_zero (v : Fin 3 → F)
    (hv : ∀ g : SL(3,F), specialLinearNatural 3 g v = v) : v = 0 :=
  SL3ParabolicNatural.line_fixed_zero v (fun g _ => hv g)

private theorem dual_fixed_zero (v : Module.Dual F (Fin 3 → F))
    (hv : ∀ g : SL(3,F), (specialLinearNatural 3).dual g v = v) : v = 0 :=
  SL3ParabolicNatural.point_dual_fixed_zero v (fun g _ => hv g)

private theorem prod_fixed_zero {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F SL(3,F) W)
    (hfix : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (v : W × W) (hv : ∀ g, (ρ.prod ρ) g v = v) : v = 0 :=
  Prod.ext (hfix v.1 (fun g => congrArg Prod.fst (hv g)))
    (hfix v.2 (fun g => congrArg Prod.snd (hv g)))

local notation "Q" => msQ K R
local notation "Z" => SourceInterface.centerIn Q
local notation "C" => Q ⊓ centralizer (K : Set G)
local notation "Phi" => frattiniIn Q
local notation "D" => Q ⊓ centralizer (Phi : Set G)
local notation "v" => specialLinearNatural (k := F) 3

/-- The whole third-row quotient puts every component-fixed element in the center. -/
theorem fixed_le_center_of_doubleDual
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Q Z (linearThreeActor e) (((v).dual.prod (v).dual))) :
    C ≤ Z :=
  fixed_le_lower hm (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (prod_fixed_zero _ dual_fixed_zero)

/-- All three whole upper sections are used to lower C_Q(K) to Z(Q). -/
theorem fixed_le_center_of_frattini_sections
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hPhi : HasSectionModel K Phi Z (linearThreeActor e) (v).dual)
    (hD : HasSectionModel K D Phi (linearThreeActor e) (((v).dual.prod (v).dual)))
    (hQ : HasSectionModel K Q D (linearThreeActor e) (((v).prod v))) :
    C ≤ Z := by
  have ha : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hCD := fixed_le_lower hQ ha (prod_fixed_zero _ natural_fixed_zero)
  have hDPhi := fixed_le_lower hD ha (prod_fixed_zero _ dual_fixed_zero)
  have hPhiZ := fixed_le_lower hPhi ha dual_fixed_zero
  intro x hx
  exact hPhiZ ⟨hDPhi ⟨hCD hx,hx.2⟩,hx.2⟩

/-- The natural-center, doubled-dual row has no component-fixed core elements. -/
theorem fixed_eq_bot_of_natural_doubleDual
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hZ : HasSectionModel K Z ⊥ (linearThreeActor e) v)
    (hQ : HasSectionModel K Q Z (linearThreeActor e) (((v).dual.prod (v).dual))) :
    C = ⊥ := by
  apply bot_unique
  intro x hx
  exact fixed_le_lower hZ (e.surjective.comp (QuotientGroup.mk'_surjective _))
    natural_fixed_zero ⟨fixed_le_center_of_doubleDual e hQ hx,hx.2⟩

variable [Finite G] [Finite F] [CharP F 2]
variable {n : ℕ} (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)

include h hn

/-- The genuine fourth-row fixed factor is the whole C_Q(K), rather than
only the fixed subgroup of its center. No ambient centrality is asserted. -/
theorem center_split_over_whole_fixed
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hU : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) v)
    (hPhi : HasSectionModel K Phi Z (linearThreeActor e) (v).dual)
    (hD : HasSectionModel K D Phi (linearThreeActor e) (((v).dual.prod (v).dual)))
    (hQ : HasSectionModel K Q D (linearThreeActor e) (((v).prod v))) :
    C = Z ⊓ centralizer (K : Set G) ∧
      Z = C ⊔ ⁅Z,K⁆ ∧ C ⊓ ⁅Z,K⁆ = ⊥ := by
  have hC : C = Z ⊓ centralizer (K : Set G) := le_antisymm
    (le_inf (fixed_le_center_of_frattini_sections e hPhi hD hQ) inf_le_right)
    (inf_le_inf_right _ (map_subtype_le _))
  have hs := NaturalCenter.center_split h hn e hU
  exact ⟨hC,by rw [hC,sup_comm]; exact hs.1.symm,by rw [hC,inf_comm]; exact hs.2⟩

/-- A natural moved center is the whole center when the core has no
component-fixed elements. This implication does not use upper-section models. -/
theorem center_eq_moved_of_fixed_eq_bot
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hU : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) v)
    (hC : C = ⊥) : Z = ⁅Z,K⁆ := by
  have hc : Z ⊓ centralizer (K : Set G) = ⊥ := bot_unique
    ((inf_le_inf_right _ (map_subtype_le _)).trans_eq hC)
  have hs := (NaturalCenter.center_split h hn e hU).1
  rw [hc,sup_bot_eq] at hs
  exact hs.symm

theorem natural_center_of_moved_of_fixed_eq_bot
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hU : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) v)
    (hC : C = ⊥) : HasSectionModel K Z ⊥ (linearThreeActor e) v := by
  rw [center_eq_moved_of_fixed_eq_bot h hn e hU hC]
  exact hU

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.FixedCore
