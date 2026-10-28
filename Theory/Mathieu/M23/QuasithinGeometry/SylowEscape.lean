module
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage.TripleLocal
public import Theory.Mathieu.M23.Properties.Automorphisms

/-! A Sylow-invariant two-local of M23 escaping every heptad stabilizer.
The certified Sylow action has orbits of sizes 1, 2, 4 and 16. Its unique
union of orbits of size at most two is a triple, preserved by its normalizer.
All M23 automorphisms are inner, so its triple stabilizer is invariant under
every Sylow-normalizing automorphism. The existing concrete local mover shows
that it cannot preserve the unique Sylow-invariant seven-point set. Sylow
conjugacy transports this construction to every prescribed Sylow subgroup.
Only bounded point-table identities use finite checking.
Source: Aschbacher--Smith 2.5.2, printed p.551. -/
public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowEscape
open FusionCertificate
open SylowTwoLocals.Coverage

private def orbitOneIndex : Fin 23 → Fin 128 := ![0, 0, 8, 16, 24, 0, 0, 32, 40, 48, 56, 0, 0, 64, 72, 80, 88, 0, 0, 96, 104, 112, 120]

private theorem orbit_one (a : Fin 23) (ha : a ∉ FourNormalizers.fixedSet) :
    pointTable (orbitOneIndex a) 1 = a := by
  revert ha a
  decide +kernel

private theorem small_orbit : ∀ a : Fin 23,
    a ∈ fixedTriple ↔ ∃ b : Fin 23, ∀ i : Fin 128,
      pointTable i a = a ∨ pointTable i a = b := by
  decide +kernel

private theorem triple_stable : ∀ (i : Fin 128) (a : Fin 23),
    a ∈ fixedTriple → pointTable i a ∈ fixedTriple := by
  decide +kernel

private def moving : M23 := ⟨CommonFour.relativePerm0,
  by
    change CommonFour.relativePerm 0 ∈ M23
    rw [CommonFour.relative_correct 0]
    exact M23.mul_mem (M23.mul_mem (M23.inv_mem CommonFour.transport.property)
      CommonFour.quintetMove.property) CommonFour.transport.property⟩

private theorem moving_triple : moving ∈ MulAction.stabilizer M23 fixedTriple := by
  apply MulAction.mem_stabilizer_finset'.mpr
  change ∀a∈fixedTriple, CommonFour.relativePerm0 a ∈ fixedTriple
  decide +kernel

private theorem moving_escape : moving ∉ MulAction.stabilizer M23 FourNormalizers.fixedSet := by
  intro h
  have hm : moving • (5 : Fin 23) ∈ FourNormalizers.fixedSet :=
    MulAction.mem_stabilizer_finset'.mp h (by decide +kernel)
  change CommonFour.relativePerm0 5 ∈ FourNormalizers.fixedSet at hm
  exact (by decide +kernel : CommonFour.relativePerm0 5 ∉ FourNormalizers.fixedSet) hm


private theorem triple_characterization (a : Fin 23) :
    a ∈ fixedTriple ↔ ∃ b : Fin 23, ∀ u ∈ subgroup, u • a = a ∨ u • a = b := by
  rw [small_orbit]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,fun u hu => ?_⟩
    obtain ⟨i,hi⟩ := exists_perm ⟨u.val,hu⟩
    change u.val a = a ∨ u.val a = b
    rw [← hi]
    exact hb i
  · rintro ⟨b,hb⟩
    exact ⟨b,fun i => hb ⟨perm i,rawSubgroup_le (perm_mem i)⟩ (perm_mem i)⟩

private theorem normalizer_triple (g : M23)
    (hg : g ∈ normalizer (subgroup : Set M23)) : g • fixedTriple = fixedTriple := by
  change g ∈ MulAction.stabilizer M23 fixedTriple
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  obtain ⟨b,hb⟩ := (triple_characterization a).mp ha
  apply (triple_characterization _).mpr
  refine ⟨g • b,fun u hu => ?_⟩
  have hv := (mem_normalizer_iff.mp ((normalizer (subgroup : Set M23)).inv_mem hg) u).mp hu
  rcases hb _ hv with h | h
  · left
    have hh := congrArg (fun x : Fin 23 => g • x) h
    simpa only [inv_inv,mul_smul,smul_inv_smul] using hh
  · right
    have hh := congrArg (fun x : Fin 23 => g • x) h
    simpa only [inv_inv,mul_smul,smul_inv_smul] using hh

private theorem sylow_le_triple : subgroup ≤ MulAction.stabilizer M23 fixedTriple := by
  intro g hg
  exact normalizer_triple g (subgroup.le_normalizer hg)

private theorem triple_invariant (α : MulAut M23)
    (hα : subgroup.map α.toMonoidHom = subgroup) :
    (MulAction.stabilizer M23 fixedTriple).map α.toMonoidHom =
      MulAction.stabilizer M23 fixedTriple := by
  obtain ⟨g,rfl⟩ := m23_conj_surjective α
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact congrArg (MulAction.stabilizer M23) (normalizer_triple g
    (mem_normalizer_iff_map_conj_eq.mpr hα))

private theorem invariant_seven_eq (B : Finset (Fin 23)) (hc : B.card = 7)
    (hP : subgroup ≤ MulAction.stabilizer M23 B) : B = FourNormalizers.fixedSet := by
  have hclosed {a : Fin 23} (ha : a ∈ B) (i : Fin 128) : pointTable i a ∈ B :=
    MulAction.mem_stabilizer_finset'.mp
      (hP (show (⟨perm i,rawSubgroup_le (perm_mem i)⟩ : M23) ∈ subgroup from perm_mem i)) ha
  have hsub : B ⊆ FourNormalizers.fixedSet := by
    intro a ha
    by_contra han
    have h1 : (1 : Fin 23) ∈ B := by
      let g : M23 := ⟨perm (orbitOneIndex a),rawSubgroup_le (perm_mem _)⟩
      have hg : g ∈ subgroup := perm_mem _
      have hb := MulAction.mem_stabilizer_finset'.mp (hP (subgroup.inv_mem hg)) ha
      have he : g • (1 : Fin 23) = a := orbit_one a han
      rw [← he, inv_smul_smul] at hb
      exact hb
    have houtside : FourNormalizers.fixedSetᶜ ⊆ B := by
      intro b hb
      have hn : b ∉ FourNormalizers.fixedSet := Finset.mem_compl.mp hb
      rw [← orbit_one b hn]
      exact hclosed h1 _
    have hd := Finset.card_le_card houtside
    have hn : FourNormalizers.fixedSetᶜ.card = 16 := by decide +kernel
    rw [hc,hn] at hd
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hc]; decide +kernel)

private theorem triple_not_le_seven (B : Finset (Fin 23)) (hc : B.card = 7) :
    ¬ MulAction.stabilizer M23 fixedTriple ≤ MulAction.stabilizer M23 B := by
  intro h
  have he := invariant_seven_eq B hc (sylow_le_triple.trans h)
  exact moving_escape (he ▸ h moving_triple)


/-- An actual Sylow-stable two-local escaping every heptad stabilizer. -/
theorem exists_invariant_local (P : Sylow 2 M23) :
    ∃ K : Subgroup M23, (P : Subgroup M23) ≤ K ∧ IsTwoLocal K ∧
      (∀ α : MulAut M23, (P : Subgroup M23).map α.toMonoidHom = P →
        K.map α.toMonoidHom = K) ∧
      ∀ B : Finset (Fin 23), B.card = 7 → ¬ K ≤ MulAction.stabilizer M23 B := by
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq M23 sylow P
  let e := MulAut.conj c
  have hP : (P : Subgroup M23) = subgroup.map e.toMonoidHom :=
    (congrArg Sylow.toSubgroup hc).symm
  let J := MulAction.stabilizer M23 fixedTriple
  let K := J.map e.toMonoidHom
  refine ⟨K,?_,Theory.GroupTheory.isTwoLocal_map e
    (triple_stabilizer_isTwoLocal fixedTriple (by decide +kernel)),?_,?_⟩
  · rw [hP]
    exact map_mono sylow_le_triple
  · intro α hα
    let β := e⁻¹ * α * e
    have hβ : subgroup.map β.toMonoidHom = subgroup := by
      change subgroup.map (e.symm.toMonoidHom.comp (α.toMonoidHom.comp e.toMonoidHom)) = _
      rw [← map_map,← map_map,← hP,hα,hP,map_map]
      simp
    have hh := triple_invariant β hβ
    have hx := congrArg (Subgroup.map e.toMonoidHom) hh
    have hecomp : e.toMonoidHom.comp β.toMonoidHom = α.toMonoidHom.comp e.toMonoidHom := by
      ext x
      dsimp [β]
      simp
    rw [map_map,hecomp,← map_map] at hx
    exact hx
  · intro B hB hle
    have hmap := map_mono (f := e.symm.toMonoidHom) hle
    have he : K.map e.symm.toMonoidHom = J := by
      dsimp [K]
      rw [map_map]
      simp
    rw [he] at hmap
    change J ≤ (MulAction.stabilizer M23 B).map (MulAut.conj c⁻¹).toMonoidHom at hmap
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj] at hmap
    exact triple_not_le_seven (c⁻¹ • B) (by simpa using hB) hmap

end Sporadic.Mathieu.M23Geometry.SylowEscape
