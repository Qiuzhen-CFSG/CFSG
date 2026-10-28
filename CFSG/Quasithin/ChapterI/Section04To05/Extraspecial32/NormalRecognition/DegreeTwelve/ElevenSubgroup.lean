module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.Interfaces
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers
public import Theory.GroupTheory.DoubleCosetCard

/-!
# Construction of the eleven-point subgroup

The local normalizer calculations supply `L`, `K`, `r`, and `v`. The relation
`vrv = rvr` and the two double cosets of `K` in `L` prove that `L ∪ LvL` is
closed under multiplication and inversion. The same relation proves
`L ∩ vLv⁻¹ = K`, so double-coset counting gives order 7920. The actual map
`lK ↦ lvL` into the left cosets of `L` identifies the action needed to lift
three-transitivity to four-transitivity.

For the final intersection with the conjugate by `z`, two possible degeneracies
must be excluded. First, `z ∈ M` would make `v` normalize `L`, contradicting
the first braid relation. Second, an element of `M ∩ zMz⁻¹` outside `L`
would place `v` in this intersection, and `(vz)³ = 1` would force `z ∈ M`.
Thus both `z ∉ M` and `M ∩ zMz⁻¹ = L` are proved, with no simplicity premise.

The final theorem constructs the commuting cubic, the marked symmetric-six
subgroup and its normalizer configuration from `Hypotheses`, relative quaternion
normality, `FusionEightData`, and the explicit earlier `SourceGeometry`.
It discharges every marked local input to the double-coset construction. The
construction of `SourceGeometry` remains with the degree-twelve assembly owner.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 4.5–4.11, pp.40–42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup DoubleCoset MulAction

variable {G : Type*} [Group G] {z : G}

namespace MarkedLocalData
variable (c : MarkedLocalData z)

private theorem v_inv : c.v⁻¹ = c.v := (inv_eq_iff_mul_eq_one).mpr c.v_sq

private theorem conj_K {x : G} (hx : x ∈ c.K) : c.v * x * c.v ∈ c.K := by
  simpa only [c.v_inv] using (mem_normalizer_iff.mp c.v_normalizes x).mp hx

private theorem sandwich_r_not_mem : c.v * c.r * c.v ∉ c.L := by
  intro hr
  rw [c.braid] at hr
  exact c.v_not_mem ((c.L.mul_mem_cancel_left c.r_mem).mp
    ((c.L.mul_mem_cancel_right c.r_mem).mp hr))

/-- The marked local subgroup is the actual conjugate intersection. The braid
relation rules out the larger-intersection case. -/
public theorem intersection_v : c.L ⊓ c.L.map (MulAut.conj c.v).toMonoidHom = c.K := by
  apply le_antisymm
  · intro x hx
    have hxv : x ∈ c.L.map (MulAut.conj c.v).toMonoidHom := hx.2
    have hvx : c.v * x * c.v ∈ c.L := by
      rw [mem_map_equiv] at hxv
      simpa only [mem_map_equiv, MulAut.conj_symm_apply, c.v_inv] using hxv
    rcases c.cover x hx.1 with hxK | hxK
    · exact hxK
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hxK
      have he : c.v * (a * c.r * b) * c.v =
          (c.v * a * c.v) * (c.v * c.r * c.v) * (c.v * b * c.v) := by
        simp only [mul_assoc, ← mul_assoc c.v c.v, c.v_sq, one_mul]
      rw [he] at hvx
      exact False.elim (c.sandwich_r_not_mem
        ((c.L.mul_mem_cancel_left (c.le (c.conj_K ha))).mp
          ((c.L.mul_mem_cancel_right (c.le (c.conj_K hb))).mp hvx)))
  · intro x hx
    refine ⟨c.le hx, ?_⟩
    change x ∈ c.L.map (MulAut.conj c.v).toMonoidHom
    rw [mem_map_equiv]
    simpa only [MulAut.conj_symm_apply, c.v_inv] using c.le (c.conj_K hx)

private def carrier : Set G := (c.L : Set G) ∪ doubleCoset c.v c.L c.L

private theorem carrier_mul_left {a x : G} (ha : a ∈ c.L) (hx : x ∈ c.carrier) :
    a * x ∈ c.carrier := by
  rcases hx with hx | hx
  · exact Or.inl (c.L.mul_mem ha hx)
  · obtain ⟨l, hl, m, hm, rfl⟩ := mem_doubleCoset.mp hx
    exact Or.inr (mem_doubleCoset.mpr ⟨a * l, c.L.mul_mem ha hl, m, hm, by group⟩)

private theorem carrier_mul_right {a x : G} (ha : a ∈ c.L) (hx : x ∈ c.carrier) :
    x * a ∈ c.carrier := by
  rcases hx with hx | hx
  · exact Or.inl (c.L.mul_mem hx ha)
  · obtain ⟨l, hl, m, hm, rfl⟩ := mem_doubleCoset.mp hx
    exact Or.inr (mem_doubleCoset.mpr ⟨l, hl, m * a, c.L.mul_mem hm ha, by group⟩)

private theorem sandwich_mem {l : G} (hl : l ∈ c.L) : c.v * l * c.v ∈ c.carrier := by
  rcases c.cover l hl with hk | hk
  · exact Or.inl (c.le (c.conj_K hk))
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hk
    have he : c.v * (a * c.r * b) * c.v =
        ((c.v * a * c.v) * c.r) * c.v * (c.r * (c.v * b * c.v)) := by
      calc
        _ = (c.v * a * c.v) * (c.v * c.r * c.v) * (c.v * b * c.v) := by
          simp only [mul_assoc, ← mul_assoc c.v c.v, c.v_sq, one_mul]
        _ = _ := by rw [c.braid]; group
    exact Or.inr (mem_doubleCoset.mpr
      ⟨(c.v * a * c.v) * c.r, c.L.mul_mem (c.le (c.conj_K ha)) c.r_mem,
        c.r * (c.v * b * c.v), c.L.mul_mem c.r_mem (c.le (c.conj_K hb)), he⟩)

/-- The subgroup constructed in source 4.10, with carrier `L ∪ LvL`. -/
public def subgroup : Subgroup G where
  carrier := c.carrier
  one_mem' := Or.inl c.L.one_mem
  mul_mem' := by
    intro x y hx hy
    rcases hx with hx | hx
    · exact c.carrier_mul_left hx hy
    rcases hy with hy | hy
    · exact c.carrier_mul_right hy (Or.inr hx)
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
    obtain ⟨d, hd, e, he, rfl⟩ := mem_doubleCoset.mp hy
    have hm := c.carrier_mul_left ha
      (c.carrier_mul_right he (c.sandwich_mem (c.L.mul_mem hb hd)))
    convert hm using 1
    group
  inv_mem' := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (c.L.inv_mem hx)
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
      exact Or.inr (mem_doubleCoset.mpr
        ⟨b⁻¹, c.L.inv_mem hb, a⁻¹, c.L.inv_mem ha, by simp [c.v_inv, mul_assoc]⟩)

/-- Exact double-coset membership in the constructed subgroup. -/
public theorem mem_subgroup (x : G) : x ∈ c.subgroup ↔ x ∈ c.L ∨ x ∈ doubleCoset c.v c.L c.L := Iff.rfl

/-- The marked subgroup of order 720 embeds in the constructed subgroup. -/
public theorem le_subgroup : c.L ≤ c.subgroup := fun _ hx => Or.inl hx

/-- The second double-coset representative belongs to the constructed subgroup. -/
public theorem v_mem_subgroup : c.v ∈ c.subgroup := Or.inr (mem_doubleCoset_self c.L c.L c.v)

/-- Since `z` normalizes `L` but lies outside it, the braid relation prevents
it from lying in `L ∪ LvL`. -/
public theorem z_not_mem_subgroup : z ∉ c.subgroup := by
  intro hz
  rcases hz with hz | hz
  · exact c.z_not_mem hz
  · obtain ⟨a, ha, b, hb, he⟩ := mem_doubleCoset.mp hz
    have hn := c.z_normalizes
    simp only [he] at hn
    have hv : c.v ∈ normalizer (c.L : Set G) :=
      ((normalizer _).mul_mem_cancel_left (c.L.le_normalizer ha)).mp
        (((normalizer _).mul_mem_cancel_right (c.L.le_normalizer hb)).mp hn)
    exact c.sandwich_r_not_mem (by
      simpa only [c.v_inv] using (mem_normalizer_iff.mp hv c.r).mp c.r_mem)

/-- The intersection in source 4.11. If it contained an element outside `L`,
it would contain `v`; the relation `(vz)³ = 1` would then put `z` in `M`.
This proves the strictness that maximality alone does not supply. -/
public theorem intersection_z (hz : z * z = 1) :
    c.subgroup ⊓ c.subgroup.map (MulAut.conj z).toMonoidHom = c.L := by
  have hzi : z⁻¹ = z := (inv_eq_iff_mul_eq_one).mpr hz
  have hL : c.L ≤ c.subgroup ⊓ c.subgroup.map (MulAut.conj z).toMonoidHom := by
    intro x hx
    refine ⟨c.le_subgroup hx, ?_⟩
    change x ∈ c.subgroup.map (MulAut.conj z).toMonoidHom
    rw [mem_map_equiv]
    simpa only [MulAut.conj_symm_apply, hzi] using
      c.le_subgroup ((mem_normalizer_iff.mp c.z_normalizes x).mp hx)
  apply le_antisymm _ hL
  intro x hx
  rcases hx.1 with hxL | hxL
  · exact hxL
  · obtain ⟨a, ha, b, hb, he⟩ := mem_doubleCoset.mp hxL
    have hv : c.v ∈ c.subgroup ⊓ c.subgroup.map (MulAut.conj z).toMonoidHom := by
      rw [he] at hx
      exact ((Subgroup.mul_mem_cancel_left _ (hL ha)).mp
        ((Subgroup.mul_mem_cancel_right _ (hL hb)).mp hx))
    have hvz : c.v ∈ c.subgroup.map (MulAut.conj z).toMonoidHom := hv.2
    have hconj : z * c.v * z ∈ c.subgroup := by
      rw [mem_map_equiv] at hvz
      simpa only [MulAut.conj_symm_apply, hzi] using hvz
    have hbraid : z * c.v * z = c.v * z * c.v := by
      have hc := c.vz_cube
      have he := congrArg (fun w : G => c.v * w * (z * c.v)) hc
      simpa only [pow_succ, pow_zero, mul_one, mul_assoc, ← mul_assoc c.v c.v,
        c.v_sq, one_mul, ← mul_assoc z z, hz] using he
    rw [hbraid] at hconj
    exact False.elim (c.z_not_mem_subgroup
      ((c.subgroup.mul_mem_cancel_left c.v_mem_subgroup).mp
        ((c.subgroup.mul_mem_cancel_right c.v_mem_subgroup).mp hconj)))

/-- The two double cosets have sizes 720 and 720²/72. -/
public theorem card_subgroup [Finite G] : Nat.card c.subgroup = 7920 := by
  have hd : Disjoint (c.L : Set G) (doubleCoset c.v c.L c.L) := by
    rw [Set.disjoint_left]
    intro x hx hd
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hd
    exact c.v_not_mem ((c.L.mul_mem_cancel_left ha).mp
      ((c.L.mul_mem_cancel_right hb).mp hx))
  have hc := card_doubleCoset_mul_card_inf c.L c.L c.v
  rw [c.intersection_v, c.card_K, c.card_L] at hc
  have hm : Nat.card c.subgroup = Nat.card c.L + Nat.card (doubleCoset c.v c.L c.L) :=
    Set.ncard_union_eq hd
  rw [hm, c.card_L]
  omega

private abbrev localSubgroup : Subgroup c.subgroup := c.L.subgroupOf c.subgroup

private def point (l : c.L) : c.subgroup :=
  ⟨(l : G) * c.v, c.subgroup.mul_mem (c.le_subgroup l.property) c.v_mem_subgroup⟩

private theorem point_eq (l n : c.L) (hln : l⁻¹ * n ∈ c.K.subgroupOf c.L) :
    (c.point l : c.subgroup ⧸ c.localSubgroup) =
      (c.point n : c.subgroup ⧸ c.localSubgroup) := by
  rw [QuotientGroup.eq]
  change ((l : G) * c.v)⁻¹ * ((n : G) * c.v) ∈ c.L
  have hk : c.v * ((l : G)⁻¹ * n) * c.v ∈ c.L := c.le (c.conj_K hln)
  simpa only [mul_inv_rev, c.v_inv, mul_assoc] using hk

private def cosetMap : (c.L ⧸ c.K.subgroupOf c.L) → (c.subgroup ⧸ c.localSubgroup) :=
  fun q => Quotient.liftOn' q (fun l => (c.point l : c.subgroup ⧸ c.localSubgroup))
    (fun l n hln => c.point_eq l n (QuotientGroup.leftRel_apply.mp hln))

private theorem cosetMap_ne_base (q : c.L ⧸ c.K.subgroupOf c.L) :
    c.cosetMap q ≠ ((1 : c.subgroup) : c.subgroup ⧸ c.localSubgroup) := by
  induction q using Quotient.inductionOn' with | h l =>
    intro he
    change (c.point l : c.subgroup ⧸ c.localSubgroup) =
      ((1 : c.subgroup) : c.subgroup ⧸ c.localSubgroup) at he
    have hm : c.point l ∈ c.localSubgroup := by
      simpa only [QuotientGroup.eq, inv_one, one_mul] using he.symm
    exact c.v_not_mem ((c.L.mul_mem_cancel_left l.property).mp hm)

private def stabilizerHom : c.L →* MulAction.stabilizer c.subgroup
    ((1 : c.subgroup) : c.subgroup ⧸ c.localSubgroup) :=
  (MulEquiv.subgroupCongr (MulAction.stabilizer_quotient c.localSubgroup).symm).toMonoidHom.comp
    (subgroupOfEquivOfLe c.le_subgroup).symm.toMonoidHom

private def puncturedCosetMap : (c.L ⧸ c.K.subgroupOf c.L) →ₑ[c.stabilizerHom]
    SubMulAction.ofStabilizer c.subgroup
      ((1 : c.subgroup) : c.subgroup ⧸ c.localSubgroup) where
  toFun q := ⟨c.cosetMap q, c.cosetMap_ne_base q⟩
  map_smul' l q := by
    apply Subtype.ext
    induction q using Quotient.inductionOn' with | h n =>
      change (c.point (l * n) : c.subgroup ⧸ c.localSubgroup) =
        ((⟨l, c.le_subgroup l.property⟩ : c.subgroup) * c.point n : c.subgroup ⧸ c.localSubgroup)
      congr 1
      apply Subtype.ext
      exact mul_assoc (l : G) n c.v

private theorem puncturedCosetMap_surjective : Function.Surjective c.puncturedCosetMap := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn' with | h m =>
    rcases (c.mem_subgroup (m : G)).mp m.property with hm | hm
    · have he : (m : c.subgroup ⧸ c.localSubgroup) = (1 : c.subgroup) := by
        rw [eq_comm, QuotientGroup.eq]
        simpa only [inv_one, one_mul] using (show m ∈ c.localSubgroup from hm)
      exact False.elim (hq he)
    · obtain ⟨a, ha, b, hb, he⟩ := mem_doubleCoset.mp hm
      refine ⟨(⟨a, ha⟩ : c.L), ?_⟩
      apply Subtype.ext
      change (c.point ⟨a, ha⟩ : c.subgroup ⧸ c.localSubgroup) = m
      rw [QuotientGroup.eq]
      change (a * c.v)⁻¹ * (m : G) ∈ c.L
      rw [he, inv_mul_cancel_left]
      exact hb

/-- The equivariant surjection `lK ↦ lvL` onto the complement of the base
coset raises three-transitivity to four-transitivity on the literal quotient. -/
public theorem four_transitive :
    MulAction.IsMultiplyPretransitive c.subgroup
      (c.subgroup ⧸ c.L.subgroupOf c.subgroup) 4 := by
  let := SubMulAction.mulAction (SubMulAction.ofStabilizer c.subgroup
    ((1 : c.subgroup) : c.subgroup ⧸ c.localSubgroup))
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (a := ((1 : c.subgroup) : c.subgroup ⧸ c.localSubgroup))).mpr
  let := c.transitive
  exact MulAction.IsPretransitive.of_embedding (f := c.puncturedCosetMap)
    c.puncturedCosetMap_surjective

/-- The marked local input produces the complete subgroup contract required
by the final degree-twelve action construction. -/
public def toElevenSubgroupData [Finite G] (hz : z * z = 1) : ElevenSubgroupData z where
  M := c.subgroup
  L := c.L
  le := c.le_subgroup
  card_M := c.card_subgroup
  card_L := c.card_L
  z_not_mem := c.z_not_mem_subgroup
  intersection := c.intersection_z hz
  transitive := c.four_transitive

end MarkedLocalData

/-- Apply the double-coset construction to the source involution. The marked
local input remains an explicit premise, to be supplied by 4.5–4.10. -/
public theorem nonempty_elevenSubgroupData_of_markedLocalData [Finite G]
    (h : Hypotheses z) (c : MarkedLocalData z) : Nonempty (ElevenSubgroupData z) := by
  have hz : z * z = 1 := by
    simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
  exact ⟨c.toElevenSubgroupData hz⟩

/-- Aschbacher 4.5–4.11: construct the subgroup of order 7920, its marked
subgroup of order 720, the four-transitive action on their literal left
quotient, and the strict conjugate intersection. The earlier source geometry
is the sole construction left explicit; the commuting cubic, marked S₆,
Aut(A₆) normalizer and M₁₀ configuration are all supplied by their producers. -/
public theorem nonempty_elevenSubgroupData [Finite G] (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) : Nonempty (ElevenSubgroupData z) := by
  obtain ⟨s⟩ := symmetricSixData h hn d a
  obtain ⟨c⟩ := nonempty_markedLocalData h hn d a s
  exact nonempty_elevenSubgroupData_of_markedLocalData h c

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
