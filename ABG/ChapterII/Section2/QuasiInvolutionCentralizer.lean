module
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section2.QuasiFrameTransport
public import ABG.ChapterII.Section2.AutomizerRestriction
public import ABG.ChapterII.Section1.Fusion

/-!
# Involution centralizers in quasi-dihedral QD-groups

For a finite group with a chosen quasi-dihedral fusion frame satisfying the
QD pattern, the centralizer of every involution is a full-Sylow Q-group.
The conclusion retains the complete Q fusion pattern and actual Sylow, four,
and quaternion subgroup witnesses. This is the quasi-dihedral branch of
Alperin--Brauer--Gorenstein, Chapter II, Section 2, Proposition 1, article
page 15 of `refs/latex/alperin-brauer-gorenstein.tex`.

The unique ambient involution class conjugates the central involution of the
chosen Sylow subgroup to the given involution. Restrict the conjugated frame
to its centralizer. The quaternion subgroup contains this involution by the
local centralizer formula of Lemma II.1.1(ii), and its normalizer fixes it by
uniqueness of the quaternion involution. Thus the outer automizer index remains
six in the centralizer. Apply the four complete fusion alternatives there:
the complement alternative has outer index two, while the QD and D alternatives
have one involution class. A central involution cannot be conjugate to a
distinct involution in the four subgroup, so only the full Q alternative remains.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_mem_small (S : Sylow 2 G) (T Q : Subgroup G)
    (hf : QuasiDihedralFusionFrame S T Q) (z : S) (hz : z ∈ Subgroup.center S) :
    (z : G) ∈ Q := by
  obtain ⟨_, _, _, _, _, _, hlocal⟩ := QuasiDihedral.four_quaternion_subgroups hf.1
  obtain ⟨eQ⟩ := hf.2.2.2.2
  have hQi : Nonempty ((Q.subgroupOf (S : Subgroup G)) ≃* QuaternionGroup 2) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hf.2.2.1).trans eQ⟩
  have hzc := Subgroup.center_le_centralizer (Q.subgroupOf (S : Subgroup G) : Set S) hz
  rw [(hlocal _ (Or.inr hQi)).1] at hzc
  obtain ⟨y, _, hy⟩ := hzc
  exact hy ▸ y.property

omit [Finite G] in
private theorem quaternion_normalizer_fixes (Q : Subgroup G) (hQ : IsQuaternionGroup Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer {z} := by
  obtain ⟨e⟩ := hQ
  intro g hg
  have hgz : g * z * g⁻¹ ∈ Q := (hg z).mp hzQ
  have he : (⟨g * z * g⁻¹, hgz⟩ : Q) = ⟨z, hzQ⟩ := by
    apply e.injective
    apply QuaternionGroup.eq_of_orderOf_eq_two
    · rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
      exact ((MulAut.conj g).orderOf_eq z).trans hz
    · rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hz
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hh : g * z * g⁻¹ = z := congrArg Subtype.val he
  exact mul_inv_eq_iff_eq_mul.mp hh

omit [Finite G] in
private theorem not_one_class_of_central_involution
    (S : Sylow 2 G) (T Q : Subgroup G) (hf : QuasiDihedralFusionFrame S T Q)
    (z : G) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center G) :
    ¬ HasElementConjugacyClassCount G 2 1 := by
  intro hc
  obtain ⟨r, _, _, hcov⟩ := hc
  obtain ⟨i, hzi⟩ := hcov z hz
  have hall (x : G) (hx : orderOf x = 2) : x = z := by
    obtain ⟨j, hxj⟩ := hcov x hx
    have hzx : IsConj z x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
    obtain ⟨g, hg⟩ := isConj_iff.mp hzx
    symm
    simpa only [Subgroup.mem_center_iff.mp hzc g, mul_assoc,
      mul_inv_cancel, mul_one] using hg
  obtain ⟨u, v, _, _, hu, hv, huv, _⟩ :=
    QuasiDihedral.four_involution_representatives (S : Subgroup G) hf.1 T hf.2.1 hf.2.2.2.1
  have hu' : (u : G) = z := hall u ((Subgroup.orderOf_coe u).trans hu)
  have hv' : (v : G) = z := hall v ((Subgroup.orderOf_coe v).trans hv)
  have huv' : u = v := Subtype.ext (hu'.trans hv'.symm)
  exact huv (huv' ▸ IsConj.refl u)

private theorem central_case (S : Sylow 2 G) (T Q : Subgroup G)
    (hf : QuasiDihedralFusionFrame S T Q) (hQ : outerAutomizerIndex Q = 6)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center S) :
    IsFullSylowQGroup (Subgroup.centralizer {(z : G)}) := by
  let C := Subgroup.centralizer {(z : G)}
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc (⟨s, hs⟩ : S)))
  have hfC := quasiDihedralFusionFrame_subtype S T Q C hSC hf
  have hQC : outerAutomizerIndex (Q.subgroupOf C) = 6 := by
    rw [outerAutomizerIndex_subgroupOf C Q
      (quaternion_normalizer_fixes Q hf.2.2.2.2 z (center_mem_small S T Q hf z hzc)
        ((Subgroup.orderOf_coe z).trans hz)), hQ]
  have hzC : (z : G) ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let zC : C := ⟨z, hzC⟩
  have hzCcent : zC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.property
  have hnot := not_one_class_of_central_involution (S.subtype hSC)
    (T.subgroupOf C) (Q.subgroupOf C) hfC zC
    ((Subgroup.orderOf_coe zC).symm.trans ((Subgroup.orderOf_coe z).trans hz)) hzCcent
  rcases quasiDihedral_fusion (S.subtype hSC) (T.subgroupOf C) (Q.subgroupOf C) hfC
    with h | h | h | h
  · exact (hnot h.2.1).elim
  · exact Or.inl ⟨S.subtype hSC, T.subgroupOf C, Q.subgroupOf C, hfC, h⟩
  · exact (hnot h.2.1).elim
  · have hbad := h.2.2.2.2
    omega

/-- ABG II.2 Proposition 1, quasi-dihedral branch: involution centralizers
satisfy the complete original Q-group definition. -/
public theorem quasiQD_involutionCentralizer_isFullSylowQGroup
    (S : Sylow 2 G) (T Q : Subgroup G)
    (hframe : QuasiDihedralFusionFrame S T Q) (hQD : QuasiDihedralQDPattern T Q)
    (x : G) (hx : orderOf x = 2) :
    IsFullSylowQGroup (Subgroup.centralizer {x}) := by
  obtain ⟨n, hn, _, a, b, ha, hb, hab, hgen⟩ := hframe.1
  let z : S := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := QuasiDihedral.half_order_pow_orderOf hn ha
  have hzc : z ∈ Subgroup.center S :=
    QuasiDihedral.half_order_pow_mem_center hn a b ha hb hab hgen
  obtain ⟨r, _, _, hcov⟩ := hQD.2.1
  obtain ⟨i, hzi⟩ := hcov z ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨j, hxj⟩ := hcov x hx
  have hzx : IsConj (z : G) x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hzx
  let e := S.equivSMul g
  let T' := T.map (MulAut.conj g).toMonoidHom
  let Q' := Q.map (MulAut.conj g).toMonoidHom
  have hf' := quasiDihedralFusionFrame_smul S T Q g hframe
  have hz' : orderOf (e z) = 2 := (e.orderOf_eq z).trans hz
  have hzc' : e z ∈ Subgroup.center (g • S : Sylow 2 G) := by
    apply Subgroup.mem_center_iff.mpr
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hzc v)
  have hQ' : outerAutomizerIndex Q' = 6 :=
    (outerAutomizerIndex_map Q (MulAut.conj g)).trans hQD.2.2.2.2
  have hh := central_case (g • S) T' Q' hf' hQ' (e z) hz' hzc'
  have he : ((e z : (g • S : Sylow 2 G)) : G) = x := hg
  rw [he] at hh
  exact hh
end ABG
