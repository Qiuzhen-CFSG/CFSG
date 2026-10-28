module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.BinaryNorm
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyProducts
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Canonical Cayley frames above ternary four-groups

An elementary four-group decomposes the split octonions into four nondegenerate
character planes. Orthogonal projection in the fixed plane gives axes `1,a`.
This plane is anisotropic exactly when `norm a = 1`; otherwise `norm a = -1`.
In the anisotropic case each character plane contains a norm-one vector: for a
nonisotropic `v` of norm minus one, `v + av` has norm one. Choose selected
vectors `b,c` in two distinct nonidentity character planes.

The ordered products `(1,a,b,ab,c,ac,bc,(ab)c)` are homogeneous, nonisotropic,
and orthogonal. Orthogonality within each plane follows from the multiplication
similarity; orthogonality between planes follows from their characters. The
binary norm calculations show that these eight axes exhaust the selected
lines. Thus the construction supplies an actual Cayley basis, including its
canonical norm-line coverage, without a conjugacy assumption.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4, and Volume II Theorem 0.1.1(4), pp.481–482.
The recognition hypotheses on p.417 are not used in this construction.
The octonion model and multiplication convention are the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.SplitOctonion
open Atlas.G2.TernaryLocals.CharacterGeometry
namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight

private theorem pair_coordinates (P : Submodule (ZMod 3) V)
    (hd : Module.finrank (ZMod 3) P = 2) {u v : V} (hu : u ∈ P) (hv : v ∈ P)
    (hi : LinearIndependent (ZMod 3) ![u, v]) {z : V} (hz : z ∈ P) :
    ∃ r s : ZMod 3, z = r • u + s • v := by
  let w : Fin 2 → P := ![⟨u, hu⟩,⟨v, hv⟩]
  have hw : LinearIndependent (ZMod 3) w := by
    apply LinearIndependent.of_comp P.subtype
    convert hi using 1
    ext i; fin_cases i <;> rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hw (by simp [hd])
  have he := congrArg Subtype.val (b.sum_repr (⟨z, hz⟩ : P))
  refine ⟨b.repr ⟨z, hz⟩ 0, b.repr ⟨z, hz⟩ 1, ?_⟩
  simpa [b, w, Fin.sum_univ_two] using he.symm

private theorem orthogonal_independent {n : Type*} (v : n → V)
    (ho : ∀ i j, i ≠ j → normPolar (v i) (v j) = 0)
    (hn : ∀ i, norm (v i) ≠ 0) : LinearIndependent (ZMod 3) v := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := normPolar)
    (fun _ _ h => ho _ _ h)
  intro i
  rw [normPolar_self]
  exact mul_ne_zero (by decide) (hn i)

private theorem fixed_axes (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : ∃ a ∈ characterSpace E 1,
      normPolar unit a = 0 ∧ norm a ≠ 0 ∧
      (∀ z ∈ characterSpace E 1, ∃ r s : ZMod 3, z = r • unit + s • a) := by
  let P := characterSpace E 1
  have hd : Module.finrank (ZMod 3) P = 2 := finrank_of_card_four E hE 1
  obtain ⟨v, hi⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ZMod 3) (by omega : 1 < Module.finrank (ZMod 3) P)
    (x := (⟨unit,unit_mem E⟩ : P)) (by simpa using (unit_ne_zero (F := ZMod 3)))
  let q : ZMod 3 := normPolar unit (v : V) / 2
  let a : V := (v : V) - q • unit
  have ha : a ∈ P := P.sub_mem v.property (P.smul_mem q (unit_mem E))
  have ho : normPolar unit a = 0 := by
    change normPolar unit ((v : V) - q • unit) = 0
    rw [map_sub, map_smul, normPolar_self]
    change normPolar unit (v : V) - q * (2 * 1) = 0
    dsimp [q]
    rw [mul_one, div_mul_cancel₀ _ (by decide : (2 : ZMod 3) ≠ 0), sub_self]
  have ha0 : a ≠ 0 := by
    intro h
    have hvq : (v : V) = q • unit := sub_eq_zero.mp h
    have hq : q • (⟨unit,unit_mem E⟩ : P) = (1 : ZMod 3) • v := by
      apply Subtype.ext
      simpa using hvq.symm
    have := (hi.eq_zero_of_pair' hq).2
    exact one_ne_zero this
  have hi' : LinearIndependent (ZMod 3) ![unit, a] := by
    apply linearIndependent_fin2.mpr
    refine ⟨ha0, ?_⟩
    intro r hr
    have hp := congrArg (normPolar unit) hr
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hp
    rw [map_smul, ho, smul_zero, normPolar_self] at hp
    exact (by decide : (0 : ZMod 3) ≠ 2) hp
  have hc := fun z hz => pair_coordinates P hd (unit_mem E) ha hi' (z := z) hz
  refine ⟨a, ha, ho, ?_, hc⟩
  intro hn
  apply ha0
  apply nondegenerate_of_span E (iSup_characterSpace_eq_top E) 1 ha
  intro z hz
  obtain ⟨r,s,rfl⟩ := hc z hz
  rw [map_add, map_smul, map_smul, normPolar_symm a unit, ho, normPolar_self, hn]
  simp

private theorem fixed_norm_iff (E : Subgroup G) (a : V)
    (ha : a ∈ characterSpace E 1) (ho : normPolar unit a = 0) (hn : norm a ≠ 0)
    (hc : ∀ z ∈ characterSpace E 1, ∃ r s : ZMod 3, z = r • unit + s • a) :
    FixedAnisotropic E ↔ norm a = 1 := by
  constructor
  · intro h
    have he := (by decide +kernel : ∀ n : ZMod 3, n ≠ 0 → n = 1 ∨ n = -1) _ hn
    rcases he with he | he
    · exact he
    have hz : norm (unit + a) = 0 := by
      rw [norm_add, ho, he]
      change (1 : ZMod 3) + -1 + 0 = 0
      ring
    have hv := h _ ((characterSpace E 1).add_mem (unit_mem E) ha) hz
    have hp := congrArg (normPolar (unit : V)) hv
    rw [map_add, ho, normPolar_self, map_zero] at hp
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 0) hp)
  · intro h z hz hzero
    obtain ⟨r,s,rfl⟩ := hc z hz
    rw [norm_orthogonal_sum unit a ho, h] at hzero
    change r^2 * 1 + s^2 * 1 = 0 at hzero
    have hrs := (by decide +kernel : ∀ r s : ZMod 3,
      r^2 * 1 + s^2 * 1 = 0 → r = 0 ∧ s = 0) r s hzero
    simp [hrs.1, hrs.2]

private theorem selected_in_character (E : Subgroup G) [IsElementaryAbelian 2 E]
    (a : V) (ha : a ∈ characterSpace E 1) (ho : normPolar unit a = 0)
    (han : FixedAnisotropic E → norm a = 1) (χ : Character E) :
    ∃ v ∈ characterSpace E χ, v ∈ selected E := by
  obtain ⟨v,hv,hn⟩ := exists_nonisotropic E χ
  by_cases hA : FixedAnisotropic E
  · by_cases hn1 : norm v = 1
    · exact ⟨v,hv,⟨χ, hv⟩,hn,fun _ => hn1⟩
    have hm : mul a v ∈ characterSpace E χ := by
      simpa only [_root_.one_mul χ] using mul_mem ha hv
    have hp : normPolar v (mul a v) = 0 := by
      simpa only [unit_mul, ho, mul_zero] using normPolar_mul_right unit a v
    have hsum : norm (v + mul a v) = 1 := by
      rw [norm_add, hp, norm_mul, han hA, one_mul, add_zero]
      exact (by decide +kernel : ∀ n : ZMod 3, n ≠ 0 → n ≠ 1 → n + n = 1) _ hn hn1
    have hs := (characterSpace E χ).add_mem hv hm
    exact ⟨v + mul a v, hs, ⟨χ,hs⟩, by rw [hsum]; exact one_ne_zero, fun _ => hsum⟩
  · exact ⟨v,hv,⟨χ, hv⟩,hn,fun h => (hA h).elim⟩

private theorem selected_axis_of_plane (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (χ : Character E) {u v : V}
    (hu : u ∈ characterSpace E χ) (hv : v ∈ characterSpace E χ)
    (hsu : u ∈ selected E) (hsv : v ∈ selected E)
    (ho : normPolar u v = 0)
    (hn : ¬ FixedAnisotropic E → norm v = -norm u)
    {x : V} (hx : x ∈ characterSpace E χ) (hsx : x ∈ selected E) :
    (∃ r : ZMod 3, x = r • u) ∨ ∃ r : ZMod 3, x = r • v := by
  have hi : LinearIndependent (ZMod 3) ![u, v] := by
    apply orthogonal_independent
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [normPolar_symm v u]
    · intro i
      fin_cases i
      · exact hsu.2.1
      · exact hsv.2.1
  obtain ⟨r,s,rfl⟩ := pair_coordinates _ (finrank_of_card_four E hE χ) hu hv hi hx
  have hrs : (r ≠ 0 ∧ s = 0) ∨ (r = 0 ∧ s ≠ 0) := by
    by_cases hA : FixedAnisotropic E
    · exact (norm_one_iff_axis u v ho (hsu.2.2 hA) (hsv.2.2 hA) r s).mp (hsx.2.2 hA)
    · exact (norm_ne_zero_iff_axis u v ho hsu.2.1 (hn hA) r s).mp hsx.2.1
  rcases hrs with h | h
  · exact Or.inl ⟨r,by simp [h.2]⟩
  · exact Or.inr ⟨s,by simp [h.1]⟩

open scoped IsMulCommutative in
private theorem four_characters (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : ∃ χ ψ : Character E,
      χ ≠ 1 ∧ ψ ≠ 1 ∧ χ ≠ ψ ∧
      χ * ψ ≠ 1 ∧ χ * ψ ≠ χ ∧ χ * ψ ≠ ψ ∧
      ∀ θ : Character E, θ = 1 ∨ θ = χ ∨ θ = ψ ∨ θ = χ * ψ := by
  classical
  let := Fintype.ofFinite (Character E)
  let : HasEnoughRootsOfUnity (ZMod 3) 2 := {
    prim := ⟨-1, IsPrimitiveRoot.neg_one 3 (by decide)⟩
    cyc := rootsOfUnity.isCyclic (ZMod 3) 2 }
  let : HasEnoughRootsOfUnity (ZMod 3) (Monoid.exponent E) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 3) (IsElementaryAbelian.exponent_dvd_p 2 E)
  have hc : Fintype.card (Character E) = 4 := by
    rw [← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity E (ZMod 3), hE]
  obtain ⟨χ,hχ⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card (Character E)) 1
  obtain ⟨ψ,_,hψ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1,χ} : Finset (Character E))) (t := Finset.univ) (by simp [Ne.symm hχ, hc])
  have hψ1 : ψ ≠ 1 := by simpa using (fun h => hψ (by simp [h]))
  have hψχ : ψ ≠ χ := by simpa using (fun h => hψ (by simp [h]))
  have hp1 : χ * ψ ≠ 1 := by
    intro h
    apply hψχ
    calc
      ψ = χ * (χ * ψ) := by rw [← _root_.mul_assoc, character_mul_self, _root_.one_mul]
      _ = χ := by rw [h, _root_.mul_one]
  have hpχ : χ * ψ ≠ χ := by simpa using hψ1
  have hpψ : χ * ψ ≠ ψ := by simpa using hχ
  refine ⟨χ, ψ, hχ, hψ1, Ne.symm hψχ, hp1, hpχ, hpψ, ?_⟩
  have hs : ({1,χ,ψ,χ * ψ} : Finset (Character E)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hc, Ne.symm hχ, Ne.symm hψ1, Ne.symm hψχ, Ne.symm hp1, Ne.symm hpχ, Ne.symm hpψ]
  intro θ
  have ht : θ ∈ ({1,χ,ψ,χ * ψ} : Finset (Character E)) := by rw [hs]; exact Finset.mem_univ θ
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ht

/-- Every elementary four-group has an orthogonal Cayley basis whose lines
are exactly the intrinsically selected homogeneous norm lines. -/
theorem exists_canonical_cayley_frame (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : ∃ a b c : V,
      a ∈ characterSpace E 1 ∧
      LinearIndependent (ZMod 3) (cayleyProducts a b c) ∧
      (∀ i j : Fin 8, i ≠ j →
        normPolar (cayleyProducts a b c i) (cayleyProducts a b c j) = 0) ∧
      (∀ i : Fin 8, cayleyProducts a b c i ∈ selected E) ∧
      ∀ x ∈ selected E, ∃ i : Fin 8, ∃ r : ZMod 3,
        x = r • cayleyProducts a b c i := by
  obtain ⟨χ,ψ,hχ,hψ,hχψ,hp1,hpχ,hpψ,hchars⟩ := four_characters E hE
  let θ : Fin 4 → Character E := ![1, χ, ψ, χ * ψ]
  have hiθ : Function.Injective θ := by
    intro i j he
    fin_cases i <;> fin_cases j <;>
      dsimp [θ] at he
    all_goals first
    | rfl
    | exact (hχ he).elim
    | exact (hχ he.symm).elim
    | exact (hψ he).elim
    | exact (hψ he.symm).elim
    | exact (hχψ he).elim
    | exact (hχψ he.symm).elim
    | exact (hp1 he).elim
    | exact (hp1 he.symm).elim
    | exact (hpχ he).elim
    | exact (hpχ he.symm).elim
    | exact (hpψ he).elim
    | exact (hpψ he.symm).elim
  obtain ⟨a,ha,hoa,hna,hca⟩ := fixed_axes E hE
  have hiff := fixed_norm_iff E a ha hoa hna hca
  have hsa : a ∈ selected E := ⟨⟨1, ha⟩,hna,hiff.mp⟩
  have hnaNeg : ¬ FixedAnisotropic E → norm a = -1 := by
    intro h
    exact (by decide +kernel : ∀ n : ZMod 3, n ≠ 0 → n ≠ 1 → n = -1)
      _ hna (fun hn => h (hiff.mpr hn))
  obtain ⟨b,hb,hsb⟩ := selected_in_character E a ha hoa hiff.mp χ
  obtain ⟨c,hc,hsc⟩ := selected_in_character E a ha hoa hiff.mp ψ
  have hab : mul a b ∈ characterSpace E χ := by
    simpa only [_root_.one_mul χ] using mul_mem ha hb
  have hac : mul a c ∈ characterSpace E ψ := by
    simpa only [_root_.one_mul ψ] using mul_mem ha hc
  have hbc : mul b c ∈ characterSpace E (χ * ψ) := mul_mem hb hc
  have habc : mul (mul a b) c ∈ characterSpace E (χ * ψ) := mul_mem hab hc
  have hsab := mul_selected E hsa hsb
  have hsac := mul_selected E hsa hsc
  have hsbc := mul_selected E hsb hsc
  have hsabc := mul_selected E hsab hsc
  have hmem (i : Fin 8) : cayleyProducts a b c i ∈
      characterSpace E (θ ⟨i.val / 2, by omega⟩) := by
    fin_cases i
    · exact unit_mem E
    · exact ha
    · exact hb
    · exact hab
    · exact hc
    · exact hac
    · exact hbc
    · exact habc
  have hsel (i : Fin 8) : cayleyProducts a b c i ∈ selected E := by
    fin_cases i
    · exact unit_selected E
    · exact hsa
    · exact hsb
    · exact hsab
    · exact hsc
    · exact hsac
    · exact hsbc
    · exact hsabc
  have hob : normPolar b (mul a b) = 0 := by
    simpa only [unit_mul, hoa, mul_zero] using normPolar_mul_right unit a b
  have hoc : normPolar c (mul a c) = 0 := by
    simpa only [unit_mul, hoa, mul_zero] using normPolar_mul_right unit a c
  have hobc : normPolar (mul b c) (mul (mul a b) c) = 0 := by
    rw [normPolar_mul_right, hob, mul_zero]
  have horth (i j : Fin 8) (hij : i ≠ j) :
      normPolar (cayleyProducts a b c i) (cayleyProducts a b c j) = 0 := by
    by_cases hp : i.val / 2 = j.val / 2
    · fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      all_goals norm_num at hp
      all_goals first
      | simpa [cayleyProducts] using hoa
      | simpa [cayleyProducts] using hob
      | simpa [cayleyProducts] using hoc
      | simpa [cayleyProducts] using hobc
      | simpa [cayleyProducts] using (normPolar_symm a unit).trans hoa
      | simpa [cayleyProducts] using (normPolar_symm (mul a b) b).trans hob
      | simpa [cayleyProducts] using (normPolar_symm (mul a c) c).trans hoc
      | simpa [cayleyProducts] using (normPolar_symm (mul (mul a b) c) (mul b c)).trans hobc
    · apply orthogonal (x := cayleyProducts a b c i) (y := cayleyProducts a b c j)
        (fun he => hp (congrArg Fin.val (hiθ he))) (hmem i) (hmem j)
  refine ⟨a,b,c,ha,orthogonal_independent _ horth (fun i => (hsel i).2.1),horth,hsel,?_⟩
  intro x hsx
  obtain ⟨φ,hx⟩ := hsx.1
  rcases hchars φ with h | h | h | h
  · rw [h] at hx
    have hn : ¬ FixedAnisotropic E → norm a = -norm (unit : V) := hnaNeg
    rcases selected_axis_of_plane E hE 1 (unit_mem E) ha (unit_selected E) hsa hoa hn hx hsx with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨0,r,hr⟩
    · exact ⟨1,r,hr⟩
  · rw [h] at hx
    have hn (hA : ¬ FixedAnisotropic E) : norm (mul a b) = -norm b := by
      rw [norm_mul, hnaNeg hA, neg_one_mul]
    rcases selected_axis_of_plane E hE χ hb hab hsb hsab hob hn hx hsx with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨2,r,hr⟩
    · exact ⟨3,r,hr⟩
  · rw [h] at hx
    have hn (hA : ¬ FixedAnisotropic E) : norm (mul a c) = -norm c := by
      rw [norm_mul, hnaNeg hA, neg_one_mul]
    rcases selected_axis_of_plane E hE ψ hc hac hsc hsac hoc hn hx hsx with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨4,r,hr⟩
    · exact ⟨5,r,hr⟩
  · rw [h] at hx
    have hn (hA : ¬ FixedAnisotropic E) : norm (mul (mul a b) c) = -norm (mul b c) := by
      rw [norm_mul, norm_mul, norm_mul, hnaNeg hA]
      ring
    rcases selected_axis_of_plane E hE (χ * ψ) hbc habc hsbc hsabc hobc hn hx hsx with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨6,r,hr⟩
    · exact ⟨7,r,hr⟩

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
