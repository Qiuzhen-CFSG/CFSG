module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootReflections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimplePanels
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The actual endpoint kernel, source local group and radical action

K_i is the core of B in the marked parabolic, embedded back into the
same finite quotient Y. The action is on the literal coset panel P_i/B.
Each canonical simple root is disjoint from K_i and acts faithfully.
The source L_i is the permutation image of <U,U^{s_i}>, not an original
factor renamed L_i. The quotient of R_i by its panel-action kernel has
its canonical faithful comparison with this L_i once U_{s_i} lies in K_i.

That last containment is the earlier local-section premise in Fong--Seitz
I (2B), used in (5C)(b); it is explicit here. From it, the finite normal
Sylow argument proves U_{s_i}=U intersect K_i and proves that the whole
parabolic normalizes this radical. Restriction constructs the actual
R_i conjugation action on U_{s_i}. Its inverse-actor formula explicitly
translates Lean's left conjugation to the source's right conjugation.
No irreducibility or elementary-abelian structure is encoded in the action.

Source: Fong--Seitz I, Section 5, printed pp.25--28, especially the
definition of L_i, (5B)--(5C), and the sections used by (5D)--(5F).
These maps anchor the structural exclusions and (6E) to the same panel,
roots, quotient and full Cartan used by the marked source configuration.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

@[expose] def endpointAction (i : Fin 2) :
    Q.tits.standardParabolic {Q.simple i} →* Equiv.Perm (Panel Q i) :=
  MulAction.toPermHom _ _

@[expose] def localKernel (i : Fin 2) : Subgroup (X ⧸ Q.D) :=
  ((Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})).normalCore).map
    (Q.tits.standardParabolic {Q.simple i}).subtype

theorem localKernel_le_borel (i : Fin 2) : localKernel Q i ≤ Q.tits.B := by
  rintro x ⟨y,hy,rfl⟩
  exact normalCore_le (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})) hy

theorem localKernel_parabolic_normalizes (i : Fin 2) :
    Q.tits.standardParabolic {Q.simple i} ≤ normalizer (localKernel Q i : Set _) := by
  intro x hx
  apply le_normalizer_map (Q.tits.standardParabolic {Q.simple i}).subtype
  refine ⟨⟨x,hx⟩, ?_, rfl⟩
  rw [Subgroup.normalizer_eq_top]
  trivial

theorem localKernel_le_conjugate_borel (i : Fin 2) :
    localKernel Q i ≤ borelConjugate (Q.simple i) := by
  let n := representative (Q.simple i)
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  intro x hx
  exact localKernel_le_borel Q i
    ((mem_normalizer_iff.mp (localKernel_parabolic_normalizes Q i hn) x).mp hx)

theorem simpleRoot_disjoint_localKernel (i : Fin 2) :
    Disjoint (simpleRoot Q split i) (localKernel Q i) :=
  (simpleRoot_disjoint_conjugateBorel Q split i).mono_right
    (localKernel_le_conjugate_borel Q i)

@[expose] def panelAction (i : Fin 2) (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ Q.tits.standardParabolic {Q.simple i}) : A →* Equiv.Perm (Panel Q i) :=
  (endpointAction Q i).comp (inclusion hA)

theorem panelAction_ker (i : Fin 2) (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ Q.tits.standardParabolic {Q.simple i}) :
    (panelAction Q i A hA).ker = (localKernel Q i).subgroupOf A := by
  ext a
  change (⟨a, hA a.property⟩ : Q.tits.standardParabolic {Q.simple i}) ∈
    (MulAction.toPermHom _ (Panel Q i)).ker ↔ (a : X ⧸ Q.D) ∈ localKernel Q i
  rw [← normalCore_eq_ker]
  constructor
  · intro ha
    exact ⟨⟨a,hA a.property⟩,ha,rfl⟩
  · rintro ⟨b,hb,he⟩
    have he' : b = ⟨a,hA a.property⟩ := Subtype.ext he
    rwa [he'] at hb

def rankOneAction (i : Fin 2) : rankOne Q split i →* Equiv.Perm (Panel Q i) :=
  panelAction Q i _ (rankOne_le_parabolic Q split i)

theorem rankOneAction_ker (i : Fin 2) :
    (rankOneAction Q split i).ker = (localKernel Q i).subgroupOf (rankOne Q split i) :=
  panelAction_ker Q i _ _

def rankOneFaithfulEquiv (i : Fin 2) :
    rankOne Q split i ⧸ (rankOneAction Q split i).ker ≃* (rankOneAction Q split i).range :=
  QuotientGroup.quotientKerEquivRange _

theorem simpleRoot_panelAction_injective (i : Fin 2) :
    Function.Injective (panelAction Q i (simpleRoot Q split i)
      ((simpleRoot_le Q split i).trans
        (split.U_le.trans (Q.tits.B_le_standardParabolic {Q.simple i})))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [panelAction_ker]
  exact subgroupOf_eq_bot.mpr (simpleRoot_disjoint_localKernel Q split i).symm

@[expose] def localClosure (i : Fin 2) : Subgroup (X ⧸ Q.D) :=
  split.U ⊔ unipotentConjugate split (Q.simple i)

theorem localClosure_le_parabolic (i : Fin 2) :
    localClosure Q split i ≤ Q.tits.standardParabolic {Q.simple i} := by
  let n := representative (Q.simple i)
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  have hU := split.U_le.trans (Q.tits.B_le_standardParabolic {Q.simple i})
  apply sup_le hU
  intro x hx
  have h := (Q.tits.standardParabolic {Q.simple i}).mul_mem
    ((Q.tits.standardParabolic {Q.simple i}).mul_mem
      ((Q.tits.standardParabolic {Q.simple i}).inv_mem hn) (hU hx)) hn
  change (n : X ⧸ Q.D)⁻¹*((n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹)*(n : X ⧸ Q.D) ∈
    Q.tits.standardParabolic {Q.simple i} at h
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

def localAction (i : Fin 2) : localClosure Q split i →* Equiv.Perm (Panel Q i) :=
  panelAction Q i _ (localClosure_le_parabolic Q split i)

/-- The source action is the restriction of the same endpoint panel action. -/
theorem localAction_eq_panelAction (i : Fin 2) :
    localAction Q split i = panelAction Q i _ (localClosure_le_parabolic Q split i) := by
  rfl

@[expose] def localGroup (i : Fin 2) : Subgroup (Equiv.Perm (Panel Q i)) :=
  (localAction Q split i).range

/-- The whole-root numerator has precisely the literal endpoint-kernel intersection. -/
theorem localAction_ker (i : Fin 2) :
    (localAction Q split i).ker = (localKernel Q i).subgroupOf (localClosure Q split i) :=
  panelAction_ker Q i _ _

/-- Source L_i as the faithful quotient of the whole-root numerator. -/
def localFaithfulEquiv (i : Fin 2) :
    localClosure Q split i ⧸ (localAction Q split i).ker ≃* localGroup Q split i :=
  QuotientGroup.quotientKerEquivRange _

theorem rankOne_le_localClosure (i : Fin 2) : rankOne Q split i ≤ localClosure Q split i :=
  sup_le_sup (simpleRoot_le Q split i) (comap_mono (simpleRoot_le Q split i))

theorem rankOne_conjugate (i : Fin 2) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    rightConjugate (rankOne Q split i) (n : X ⧸ Q.D) = rankOne Q split i := by
  change (simpleRoot Q split i ⊔ rootAt Q split i (Q.simple i)).comap
    (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom = _
  rw [← comap_sup_eq _ _ _ (MulAut.conj (n : X ⧸ Q.D)).surjective]
  change rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D) ⊔
    rightConjugate (rootAt Q split i (Q.simple i)) (n : X ⧸ Q.D) = _
  rw [← rootAt_eq Q split i (Q.simple i) n hn,
    rootAt_right Q split i (Q.simple i) (Q.simple i) n hn]
  have hs : Q.simple i*Q.simple i = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  rw [hs, rootAt_one, sup_comm]
  rfl

theorem localClosure_le_rankOne_sup_kernel (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    localClosure Q split i ≤ rankOne Q split i ⊔ localKernel Q i := by
  have hU : split.U ≤ rankOne Q split i ⊔ localKernel Q i := by
    intro x hx
    have hmem : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]
      exact hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hmem
    exact mul_mem_sup ((show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) ha)
      (hV hb)
  apply sup_le hU
  let n := representative (Q.simple i)
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  have hc := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hU
  rw [← comap_sup_eq _ _ _ (MulAut.conj (n : X ⧸ Q.D)).surjective] at hc
  change unipotentConjugate split (Q.simple i) ≤
    rightConjugate (rankOne Q split i) (n : X ⧸ Q.D) ⊔
      rightConjugate (localKernel Q i) (n : X ⧸ Q.D) at hc
  rwa [rankOne_conjugate Q split i n (representative_spec _),
    rightConjugate_eq_self _ (localKernel_parabolic_normalizes Q i hn)] at hc

theorem panelAction_range (i : Fin 2) (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ Q.tits.standardParabolic {Q.simple i}) :
    (panelAction Q i A hA).range =
      (A.subgroupOf (Q.tits.standardParabolic {Q.simple i})).map (endpointAction Q i) := by
  rw [panelAction, MonoidHom.range_comp, inclusion_range]

theorem localKernel_subgroupOf (i : Fin 2) :
    (localKernel Q i).subgroupOf (Q.tits.standardParabolic {Q.simple i}) =
      (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})).normalCore :=
  comap_map_eq_self_of_injective (Q.tits.standardParabolic {Q.simple i}).subtype_injective _

theorem rankOneAction_range_eq_localGroup (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    (rankOneAction Q split i).range = localGroup Q split i := by
  change (panelAction Q i _ _).range = (panelAction Q i _ _).range
  rw [panelAction_range, panelAction_range]
  apply le_antisymm (map_mono (subgroupOf_mono _ (rankOne_le_localClosure Q split i)))
  have hin := subgroupOf_mono (Q.tits.standardParabolic {Q.simple i})
    (localClosure_le_rankOne_sup_kernel Q split i hV)
  rw [subgroupOf_sup (rankOne_le_parabolic Q split i)
    ((localKernel_le_borel Q i).trans (Q.tits.B_le_standardParabolic {Q.simple i}))] at hin
  have hm := map_mono (f := endpointAction Q i) hin
  rw [Subgroup.map_sup, localKernel_subgroupOf, normalCore_eq_ker] at hm
  change _ ≤ _ ⊔ (endpointAction Q i).ker.map (endpointAction Q i) at hm
  simpa only [map_ker_self, sup_bot_eq] using hm

def rankOneLocalEquiv (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    rankOne Q split i ⧸ (rankOneAction Q split i).ker ≃* localGroup Q split i :=
  (rankOneFaithfulEquiv Q split i).trans
    (MulEquiv.subgroupCongr (rankOneAction_range_eq_localGroup Q split i hV))

@[simp] theorem rankOneLocalEquiv_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : rankOne Q split i) :
    (rankOneLocalEquiv Q split i hV (QuotientGroup.mk r) : Equiv.Perm (Panel Q i)) =
      rankOneAction Q split i r := by rfl

theorem unipotent_inf_kernel_le_remainder (i : Fin 2) :
    split.U ⊓ localKernel Q i ≤ simpleRemainder Q split i := by
  apply le_inf inf_le_left
  exact two_subgroup_le_conjugate split _
    (split.isTwo.of_injective (inclusion inf_le_left) (inclusion_injective _))
    (Q.simple i) (inf_le_right.trans (localKernel_le_conjugate_borel Q i))

theorem remainder_eq_unipotent_inf_kernel (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    simpleRemainder Q split i = split.U ⊓ localKernel Q i :=
  le_antisymm (le_inf inf_le_left hV) (unipotent_inf_kernel_le_remainder Q split i)

theorem remainder_parabolic_normalizes (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
  have hconj (n : X ⧸ Q.D) (hn : n ∈ Q.tits.standardParabolic {Q.simple i})
      (x : X ⧸ Q.D) (hx : x ∈ simpleRemainder Q split i) :
      n*x*n⁻¹ ∈ simpleRemainder Q split i := by
    let f := (MulAut.conj n).toMonoidHom
    have hK : (simpleRemainder Q split i).map f ≤ localKernel Q i := by
      rintro y ⟨z,hz,rfl⟩
      exact (mem_normalizer_iff.mp (localKernel_parabolic_normalizes Q i hn) z).mp (hV hz)
    have hU := two_subgroup_le_unipotent split _
      ((split.isTwo.of_injective (inclusion (show simpleRemainder Q split i ≤ split.U from
        inf_le_left)) (inclusion_injective _)).map f)
      (hK.trans (localKernel_le_borel Q i))
    rw [remainder_eq_unipotent_inf_kernel Q split i hV]
    exact ⟨hU ⟨x,hx,rfl⟩,hK ⟨x,hx,rfl⟩⟩
  intro n hn
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj n hn x
  · intro hx
    have h := hconj n⁻¹ (inv_mem hn) (n*x*n⁻¹) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

def radicalAction (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    rankOne Q split i →* MulAut (simpleRemainder Q split i) :=
  (simpleRemainder Q split i).normalizerMonoidHom.comp
    (inclusion ((rankOne_le_parabolic Q split i).trans
      (remainder_parabolic_normalizes Q split i hV)))

@[simp] theorem radicalAction_apply (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (r : rankOne Q split i) (v : simpleRemainder Q split i) :
    (radicalAction Q split i hV r v : X ⧸ Q.D) = (r : X ⧸ Q.D)*v*(r : X ⧸ Q.D)⁻¹ := by
  rfl

theorem radicalAction_right_conjugation (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (r : rankOne Q split i) (v : simpleRemainder Q split i) :
    (radicalAction Q split i hV r⁻¹ v : X ⧸ Q.D) = (r : X ⧸ Q.D)⁻¹*v*(r : X ⧸ Q.D) := by
  rw [radicalAction_apply, coe_inv, inv_inv]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
