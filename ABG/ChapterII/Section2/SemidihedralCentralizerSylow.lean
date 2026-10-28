module
public import ABG.ChapterII.Section2.SylowShapeTransport
public import ABG.ChapterII.Section1.Center

/-!
# Semidihedral Sylow subgroups in involution centralizers

In a QD-group with a supplied semidihedral Sylow subgroup S, every
involution centralizer contains an ambient Sylow isomorphic to S.
Conjugate the central involution of S to the prescribed involution, using
QD fusion, and restrict that same conjugate Sylow to the centralizer.
This retains an actual equivalence with S and requires no odd-core
hypothesis.

Source: ABG II.1 Lemma 1(v) and Proposition 1, and II.2 Proposition 1.
-/

namespace ABG

public theorem IsQDGroup.exists_semidihedral_sylow_in_centralizer
    {G : Type*} [Group G] [Finite G]
    (hQD : IsQDGroup G) (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) :
    ∃ T : Sylow 2 (Subgroup.centralizer ({x} : Set G)),
      Stellmacher.IsSemidihedralGroup T ∧ Nonempty (S ≃* T) := by
  classical
  have hS0 := hS
  obtain ⟨n, hn, _, a, b, ha, hb, hab, hgen⟩ := hS
  let z : S := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := QuasiDihedral.half_order_pow_orderOf hn ha
  have hzc : z ∈ Subgroup.center S :=
    QuasiDihedral.half_order_pow_mem_center hn a b ha hb hab hgen
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hzi⟩ := hcov z ((Subgroup.orderOf_coe z).trans hz)
  obtain ⟨j, hxj⟩ := hcov x hx
  have hzx : IsConj (z : G) x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hzx
  let e := S.equivSMul g
  have hT : Stellmacher.IsSemidihedralGroup (g • S : Sylow 2 G) :=
    semidihedral_equiv e hS0
  have hzc' : e z ∈ Subgroup.center (g • S : Sylow 2 G) := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hzc s)
  have he : ((e z : (g • S : Sylow 2 G)) : G) = x := hg
  let C := Subgroup.centralizer ({x} : Set G)
  have hTC : ((g • S : Sylow 2 G) : Subgroup G) ≤ C := by
    intro t ht
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc' (⟨t, ht⟩ : (g • S : Sylow 2 G)))
    change t * (e z).val = (e z).val * t at hh
    simpa only [he] using hh
  let T := (g • S : Sylow 2 G).subtype hTC
  let eT : T ≃* (g • S : Sylow 2 G) := Subgroup.subgroupOfEquivOfLe hTC
  exact ⟨T, semidihedral_equiv eT.symm hT, ⟨e.trans eT.symm⟩⟩

end ABG
