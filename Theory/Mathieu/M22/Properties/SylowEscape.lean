module
public import Theory.Mathieu.M22.Properties.FourNormalizers.FixedSylow
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Theory.GroupTheory.TwoLocalTransport
public import Theory.GroupTheory.SylowKernelCore
/-!
# A Sylow-invariant local subgroup escaping every hexad

The fixed Sylow has a unique orbit of size at most two. Its pair stabilizer
is therefore invariant under every Sylow-preserving automorphism. The
normalizer of the two-core of that stabilizer is an actual two-local with
the same invariance. No six-set is fixed by the pair stabilizer: the Sylow
forces the standard hexad, and the induced symmetric-five action moves it.
Sylow conjugacy transports this construction to every original Sylow.

Source: Aschbacher--Smith, Lemma 2.5.2, printed p.551, applied to the
hexad intersection in 2.3.9(7)(f).
-/
public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M22SylowEscape
open M22ValueBound.Concrete M22EvenGeometry M22FourNormalizers.FixedSylow

private def orbitZeroIndex : Fin 22 → Fin 128 := ![0, 0, 0, 0, 8, 16, 24, 32, 40, 48, 0, 56, 64, 72, 80, 88, 96, 104, 0, 112, 0, 120]
private theorem orbit_zero (a : Fin 22) (ha : a ∉ m22Hexad123) :
    rowTable (orbitZeroIndex a) 0 = a := by
  revert ha a
  decide +kernel
private theorem small_orbit : ∀ a : Fin 22,
    a ∈ m22Pair12 ↔ ∃ b : Fin 22, ∀ i : Fin 128,
      rowTable i a = a ∨ rowTable i a = b := by decide +kernel

private theorem pair_characterization (a : Fin 22) :
    a ∈ m22Pair12 ↔ ∃ b : Fin 22, ∀ u ∈ (sylow : Subgroup M22),
      u • a = a ∨ u • a = b := by
  rw [small_orbit]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,fun u hu => ?_⟩
    obtain ⟨i,hi⟩ := rowSylow_surjective ⟨u,hu⟩
    have he := congrArg Subtype.val hi
    change rowElement i = u at he
    rw [← he]
    change (rowElement i).val a = a ∨ (rowElement i).val a = b
    rw [rowElement_apply]
    exact hb i
  · rintro ⟨b,hb⟩
    refine ⟨b,fun i => ?_⟩
    have hh := hb (rowElement i) (wordElement_mem _)
    simpa only [show (rowElement i) • a = rowTable i a from rowElement_apply i a] using hh

private theorem pair_invariant (α : MulAut M22)
    (hα : (sylow : Subgroup M22).map α.toMonoidHom = sylow) :
    first.map α.toMonoidHom = first := by
  obtain ⟨g,hg⟩ := designAutEquiv.surjective α
  let σ : Equiv.Perm (Fin 22) := g.val
  have ha (u : M22) : (α u).val = σ * u.val * σ⁻¹ := by
    rw [← hg]
    exact m22DesignAutToAut_apply_perm g u
  have compat (u : M22) (a : Fin 22) : (α u) • σ a = σ (u • a) := by
    change (α u).val (σ a) = σ (u.val a)
    rw [ha]
    simp
  have hsigma : ∀ a ∈ m22Pair12, σ a ∈ m22Pair12 := by
    intro a ha
    obtain ⟨b,hb⟩ := (pair_characterization a).mp ha
    apply (pair_characterization _).mpr
    refine ⟨σ b,fun u hu => ?_⟩
    have hv : α.symm u ∈ (sylow : Subgroup M22) := by
      rw [← mem_map_equiv,hα]
      exact hu
    have hh := hb _ hv
    have he := compat (α.symm u) a
    rw [α.apply_symm_apply] at he
    rw [he]
    exact hh.elim (fun h => Or.inl (congrArg σ h)) (fun h => Or.inr (congrArg σ h))
  have hs : σ • m22Pair12 = m22Pair12 := MulAction.mem_stabilizer_finset'.mpr hsigma
  have hi : ∀a∈m22Pair12, σ.symm a ∈ m22Pair12 := by
    intro a ha
    have hm : a ∈ σ • m22Pair12 := hs.symm ▸ ha
    obtain ⟨b,hb,he⟩ := Finset.mem_smul_finset.mp hm
    have he' : σ.symm a = b := by
      change σ b = a at he
      rw [← he,σ.symm_apply_apply]
    exact he'.symm ▸ hb
  apply eq_of_le_of_card_ge ?_ (card_map_of_injective α.injective).ge
  rintro _ ⟨u,hu,rfl⟩
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a hma
  change (α u).val a ∈ m22Pair12
  rw [ha]
  exact hsigma _ (MulAction.mem_stabilizer_finset'.mp hu (hi a hma))


private theorem invariant_six_eq (B : Finset (Fin 22)) (hc : B.card = 6)
    (hP : (sylow : Subgroup M22) ≤ MulAction.stabilizer M22 B) : B = m22Hexad123 := by
  have hclosed {a : Fin 22} (ha : a ∈ B) (i : Fin 128) : rowTable i a ∈ B := by
    have hh := MulAction.mem_stabilizer_finset'.mp (hP (wordElement_mem (rowWord i))) ha
    change (rowElement i).val a ∈ B at hh
    rwa [rowElement_apply] at hh
  have hsub : B ⊆ m22Hexad123 := by
    intro a ha
    by_contra han
    have h0 : (0 : Fin 22) ∈ B := by
      let g : M22 := rowElement (orbitZeroIndex a)
      have hg : g ∈ (sylow : Subgroup M22) := wordElement_mem _
      have hb := MulAction.mem_stabilizer_finset'.mp
        (hP ((sylow : Subgroup M22).inv_mem hg)) ha
      have he : g • (0 : Fin 22) = a :=
        (rowElement_apply _ _).trans (orbit_zero a han)
      rw [← he,inv_smul_smul] at hb
      exact hb
    have houtside : m22Hexad123ᶜ ⊆ B := by
      intro b hb
      have hn : b ∉ m22Hexad123 := Finset.mem_compl.mp hb
      rw [← orbit_zero b hn]
      exact hclosed h0 _
    have hd := Finset.card_le_card houtside
    have hn : m22Hexad123ᶜ.card = 16 := by decide +kernel
    rw [hc,hn] at hd
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hc]; decide +kernel)

private theorem first_not_le_six (B : Finset (Fin 22)) (hc : B.card = 6) :
    ¬ first ≤ MulAction.stabilizer M22 B := by
  intro h
  have he := invariant_six_eq B hc ((show (sylow : Subgroup M22) ≤ first from inf_le_left).trans h)
  rw [he] at h
  have hm : m22Hexad123 ∈ m22Blocks.filter (m22Pair12 ⊆ ·) :=
    Finset.mem_filter.mpr ⟨m22Hexad123_mem,by decide +kernel⟩
  rw [pairHexads_complete] at hm
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  obtain ⟨j,hji⟩ := exists_ne i
  obtain ⟨u,hu⟩ := pairAction_surjective (Equiv.swap i j)
  apply hji
  apply pairHexad_injective
  calc
    pairHexad j = pairHexad (pairAction u i) := by rw [hu,Equiv.swap_apply_left]
    _ = u.val • pairHexad i := pairAction_spec u i
    _ = pairHexad i := by rw [hi]; exact h u.property


private theorem normalizer_invariant (α : MulAut M22)
    (hα : (sylow : Subgroup M22).map α.toMonoidHom = sylow) :
    (normalizer (pairKernel : Set M22)).map α.toMonoidHom =
      normalizer (pairKernel : Set M22) := by
  rw [map_equiv_normalizer_eq]
  have hk : pairKernel.map α.toMonoidHom = pairKernel := by
    rw [pairKernel_eq_twoCore_image]
    change (first.pCoreIn 2).map α.toMonoidHom = first.pCoreIn 2
    rw [map_pCoreIn_of_injective 2 first α.toMonoidHom α.injective,
      pair_invariant α hα]
  rw [hk]

theorem exists_invariant_local (P : Sylow 2 M22) :
    ∃ K : Subgroup M22, (P : Subgroup M22) ≤ K ∧ IsTwoLocal K ∧
      (∀ α : MulAut M22, (P : Subgroup M22).map α.toMonoidHom = P →
        K.map α.toMonoidHom = K) ∧
      ∀ B : Finset (Fin 22), B.card = 6 →
        ¬ K ≤ MulAction.stabilizer M22 B := by
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq M22 sylow P
  let e := MulAut.conj c
  let J := normalizer (pairKernel : Set M22)
  have hPJ : (sylow : Subgroup M22) ≤ J :=
    (show (sylow : Subgroup M22) ≤ first from inf_le_left).trans
      first_le_pairKernel_normalizer
  have hlocal : IsTwoLocal J :=
    ⟨pairKernel,pairKernel_ne_bot,pairKernel_isTwoGroup,rfl⟩
  have hP : (P : Subgroup M22) =
      (sylow : Subgroup M22).map e.toMonoidHom :=
    (congrArg Sylow.toSubgroup hc).symm
  let K := J.map e.toMonoidHom
  refine ⟨K,?_,Theory.GroupTheory.isTwoLocal_map e hlocal,?_,?_⟩
  · rw [hP]; exact map_mono hPJ
  · intro α hα
    let β := e⁻¹ * α * e
    have hβ : (sylow : Subgroup M22).map β.toMonoidHom = sylow := by
      change (sylow : Subgroup M22).map
        (e.symm.toMonoidHom.comp (α.toMonoidHom.comp e.toMonoidHom)) = _
      rw [← map_map,← map_map,← hP,hα,hP,map_map]
      simp
    have hx := congrArg (Subgroup.map e.toMonoidHom)
      (normalizer_invariant β hβ)
    have hecomp : e.toMonoidHom.comp β.toMonoidHom =
        α.toMonoidHom.comp e.toMonoidHom := by
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
    change J ≤ (MulAction.stabilizer M22 B).map
      (MulAut.conj c⁻¹).toMonoidHom at hmap
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj] at hmap
    exact first_not_le_six (c⁻¹ • B) (by simpa using hB)
      (first_le_pairKernel_normalizer.trans hmap)

end Sporadic.Mathieu.M22SylowEscape
