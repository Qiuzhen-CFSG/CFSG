module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient
public import Theory.AlgebraicGroup.Reductive.ConnectedRadicalQuotient

/-!
Algebraic tools for Borel's centralizer-radical argument (Chapter IV, 13.16–13.17).

The product of a connected normal solvable subgroup with a Borel is closed,
connected and solvable, so the normal subgroup lies in the Borel. Consequently
connected unipotent subgroups lying in every torus-containing Borel lie in the
unipotent radical of `I(T)`. Ambient normality of that radical kills them in a
reductive group. The separate vanishing criterion turns triviality of connected
normal unipotent subgroups into reductivity via the radical quotient theorem.

The geometric normality premise remains explicit. These tools can be imported
by the geometry proofs without depending on their final assembly module.
-/

universe u
set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Connected normal solvable subgroups lie in every Borel subgroup. -/
public theorem normal_connected_solvable_le_borel
    {G : Variety k} [AlgebraicGroup G]
    (N B : ClosedSubgroup G) (hNn : N.toSubgroup.Normal)
    (hNc : _root_.IsConnected (N : Set (Variety.Point G)))
    (hNs : Group.IsSolvable (Variety.Point N.carrierVariety))
    (hB : IsBorelSubgroup B) : N ≤ B := by
  let : N.toSubgroup.Normal := hNn
  obtain ⟨m, hm⟩ :=
    exists_closedSubgroup_productMorphism_range_eq_pointwise_mul N B
  have hclosed : IsZariskiClosed G
      ((N.toSubgroup ⊔ B.toSubgroup : Subgroup (Variety.Point G)) :
        Set (Variety.Point G)) := by
    apply Variety.isClosed_iff_isZariskiClosed.mp
    apply constructible_subgroup_isClosed G
    rw [Subgroup.normal_mul, ← hm]
    exact m.range_isConstructible
  let P : ClosedSubgroup G :=
    ClosedSubgroup.ofSubgroup (N.toSubgroup ⊔ B.toSubgroup) hclosed
  have hPc : _root_.IsConnected (P : Set (Variety.Point G)) := by
    change _root_.IsConnected
      ((N.toSubgroup ⊔ B.toSubgroup : Subgroup (Variety.Point G)) :
        Set (Variety.Point G))
    rw [Subgroup.normal_mul]
    let A : N.toSubgroup → Set (Variety.Point G) := fun n =>
      (N.toSubgroup : Set (Variety.Point G)) ∪
        (fun b : Variety.Point G => n.1 * b) ''
          (B.toSubgroup : Set (Variety.Point G))
    have hA (n : N.toSubgroup) : _root_.IsConnected (A n) := by
      apply hNc.union
      · exact ⟨n.1, n.2, ⟨1, B.toSubgroup.one_mem, by simp⟩⟩
      · exact hB.connected.image _ (continuous_const_mul n.1).continuousOn
    have hinter : (⋂ n, A n).Nonempty := by
      refine ⟨1, ?_⟩
      rw [Set.mem_iInter]
      intro n
      exact Or.inl N.toSubgroup.one_mem
    have hunion : _root_.IsConnected (⋃ n, A n) := by
      refine ⟨?_, isPreconnected_iUnion hinter fun n => (hA n).isPreconnected⟩
      refine ⟨1, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨(1 : N.toSubgroup), Or.inl N.toSubgroup.one_mem⟩
    have heq : (⋃ n, A n) =
        (N.toSubgroup : Set (Variety.Point G)) *
          (B.toSubgroup : Set (Variety.Point G)) := by
      ext g
      constructor
      · intro hg
        rw [Set.mem_iUnion] at hg
        rcases hg with ⟨n, hg | ⟨b, hb, rfl⟩⟩
        · exact ⟨g, hg, 1, B.toSubgroup.one_mem, mul_one g⟩
        · exact ⟨n.1, n.2, b, hb, rfl⟩
      · rintro ⟨n, hn, b, hb, rfl⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨n, hn⟩, Or.inr ⟨b, hb, rfl⟩⟩
    exact heq ▸ hunion
  have hPs : Group.IsSolvable (Variety.Point P.carrierVariety) := by
    let : Group.IsSolvable N.toSubgroup := by
      let : Group.IsSolvable (Variety.Point N.carrierVariety) := hNs
      exact Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv N.pointEquiv).toMonoidHom)
        (Equiv.mulEquiv N.pointEquiv).surjective
    let : Group.IsSolvable B.toSubgroup := by
      let : Group.IsSolvable (Variety.Point B.carrierVariety) := hB.solvable
      exact Group.isSolvable_of_surjective
        (f := (Equiv.mulEquiv B.pointEquiv).toMonoidHom)
        (Equiv.mulEquiv B.pointEquiv).surjective
    let L := N.toSubgroup ⊔ B.toSubgroup
    let NL : Subgroup L := N.toSubgroup.subgroupOf L
    let : NL.Normal := inferInstance
    let q := QuotientGroup.mk' NL
    let j : B.toSubgroup →* L := Subgroup.inclusion le_sup_right
    let qB : B.toSubgroup →* L ⧸ NL := q.comp j
    have hqB : Function.Surjective qB := by
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective NL y
      have hl : l.1 ∈ (N.toSubgroup : Set (Variety.Point G)) *
          (B.toSubgroup : Set (Variety.Point G)) := by
        rw [← Subgroup.normal_mul N.toSubgroup B.toSubgroup]
        exact l.2
      rcases hl with ⟨n, hn, b, hb, hnb⟩
      refine ⟨⟨b, hb⟩, ?_⟩
      apply (QuotientGroup.eq_iff_div_mem).2
      change (⟨b, (show B.toSubgroup ≤ L from le_sup_right) hb⟩ : L) / l ∈ NL
      change b / l.1 ∈ N.toSubgroup
      rw [← hnb]
      simpa using N.toSubgroup.inv_mem hn
    let : Group.IsSolvable (L ⧸ NL) := Group.isSolvable_of_surjective hqB
    have hLs : Group.IsSolvable L := by
      apply Group.isSolvable_of_ker_le_range (Subgroup.inclusion le_sup_left) q
      simp [q, NL, L]
    let : Group.IsSolvable P.toSubgroup := hLs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Equiv.mulEquiv P.pointEquiv).toMonoidHom)
      (Equiv.mulEquiv P.pointEquiv).injective
  have hBP : B ≤ P := by
    change B.toSubgroup ≤ N.toSubgroup ⊔ B.toSubgroup
    exact le_sup_right
  have hPB : P = B := hB.maximal P hPc hPs hBP
  have hNP : N ≤ P := by
    change N.toSubgroup ≤ N.toSubgroup ⊔ B.toSubgroup
    exact le_sup_left
  exact hPB ▸ hNP

/-- The vanishing criterion for the connected unipotent radical. -/
public theorem isReductive_of_connected_normal_unipotent_trivial
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G)
    (htrivial : ∀ U : ClosedSubgroup G, U.toSubgroup.Normal →
      _root_.IsConnected (U : Set (Variety.Point G)) →
      IsUnipotentAlgebraicGroup U.carrierVariety → U.toSubgroup = ⊥) :
    IsReductiveAlgebraicGroup G := by
  obtain ⟨U, hU⟩ := exists_connectedUnipotentRadicalOf
    (ClosedSubgroup.top : ClosedSubgroup G)
  have hUn : U.toSubgroup.Normal := by
    constructor
    intro x hx g
    exact (Subgroup.mem_normalizer_iff.mp
      (hU.2.2.2.1 (show g ∈ ClosedSubgroup.top from trivial)) x).mp hx
  have hUbot := htrivial U hUn hU.2.1 hU.2.2.1
  apply isReductive_of_connectedUnipotentRadical_kernel hG U hU
    (AlgebraicGroup.Morphism.id G) (fun x => ⟨x, rfl⟩)
  rw [hUbot]
  exact (AlgebraicGroup.Morphism.id G).onPoints.ker_eq_bot Function.injective_id

omit [IsAlgClosed k] in
/-- Inclusion in all torus-containing Borels is inclusion in their actual
intersection, with no normality assumption. -/
public theorem le_borelIntersection_of_forall
    {G : Variety k} [AlgebraicGroup G] (A T : ClosedSubgroup G)
    (hA : ∀ B : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B → A ≤ B) :
    A ≤ borelIntersection T := by
  change A.toSubgroup ≤ (borelIntersection T).toSubgroup
  rw [borelIntersection_toSubgroup]
  exact le_iInf fun B => hA B.1 B.2.1 B.2.2

/-- The identity component of the intersection of all Borels containing a
torus is connected and solvable. This only uses existence of one such Borel. -/
public theorem torusBorelIntersection_connected_solvable
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G)
    (hT : IsSubtorus T) :
    _root_.IsConnected (torusBorelIntersection T : Set (Variety.Point G)) ∧
      Group.IsSolvable (Variety.Point (torusBorelIntersection T).carrierVariety) := by
  have hTc : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  have hTs : Group.IsSolvable (Variety.Point T.carrierVariety) := by
    exact Group.isSolvable_of_comm
      (isMulCommutative_iff.mp hT.isMulCommutative)
  obtain ⟨B, hB, hTB⟩ :=
    exists_borelSubgroup_containing_connected_solvable T hTc hTs
  have hIB : torusBorelIntersection T ≤ B := by
    rw [torusBorelIntersection_eq_identityComponentAmbient]
    intro x hx
    have hxI := (borelIntersection T).identityComponentAmbient_le hx
    change x ∈ (borelIntersection T).toSubgroup at hxI
    rw [borelIntersection_toSubgroup] at hxI
    exact (iInf_le (fun D : BorelContainingIndex T => D.1.toSubgroup)
      ⟨B, hB, hTB⟩) hxI
  refine ⟨?_, ?_⟩
  · rw [torusBorelIntersection_eq_identityComponentAmbient]
    exact (borelIntersection T).identityComponentAmbient_isConnected
  let f := (torusBorelIntersection T).inclusion.codRestrictClosedSubgroup B
    (fun x => hIB ((torusBorelIntersection T).pointEquiv x).property)
  have hf : Function.Injective f.onPoints := by
    intro x y hxy
    apply (torusBorelIntersection T).inclusion_injective
    exact congrArg B.inclusion.onPoints hxy
  let : Group.IsSolvable (Variety.Point B.carrierVariety) := hB.solvable
  exact Group.isSolvable_of_isSolvable_injective hf

/-- In a reductive group, a connected unipotent subgroup lying in every
`T`-containing Borel is trivial, provided the unipotent radical of `I(T)` is
ambient normal. The normality premise is the missing geometric step of 13.16. -/
public theorem unipotent_eq_bot_of_borel_containment_of_intersection_radical_normal
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) (T A : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (hAc : _root_.IsConnected (A : Set (Variety.Point G)))
    (hAu : IsUnipotentAlgebraicGroup A.carrierVariety)
    (hAB : ∀ B : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B → A ≤ B)
    (hnormal : ∀ U : ClosedSubgroup G,
      IsUnipotentRadicalOf (torusBorelIntersection T) U → U.toSubgroup.Normal) :
    A.toSubgroup = ⊥ := by
  obtain ⟨hIc, hIs⟩ := torusBorelIntersection_connected_solvable T hT
  obtain ⟨U, hU, hUc⟩ := exists_unipotentRadical_of_connected_solvable
    (torusBorelIntersection T) hIc hIs
  have hAI : A ≤ torusBorelIntersection T := by
    rw [torusBorelIntersection_eq_identityComponentAmbient]
    exact connected_closedSubgroup_le_identityComponentAmbient
      A (borelIntersection T) hAc (le_borelIntersection_of_forall A T hAB)
  have hAU : A ≤ U :=
    hU.contains_unipotent_closedSubgroup hIc hIs hAI hAu
  have hUbot := connectedRadical_eq_bot_of_reductive hG U
    (hnormal U hU) hUc hU.2.1
  apply le_antisymm
  · exact hUbot ▸ hAU
  · exact bot_le

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry
