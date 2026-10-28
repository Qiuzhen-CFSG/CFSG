module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Strict cube-invariant subspaces of the six-letter covers

Let D be the three-transposition cube and D ≤ R ≤ S₄ × S₂. An
R-invariant subspace containing C(R), of index greater than two in either
the augmentation core or its natural quotient, is fixed by D.
A core vector outside C(D), together with its image under (01) or (23),
the constant vector and the last duad vector, has sixteen distinct binary
linear combinations. The natural case lifts through the constant line.
The same statement is transported through an arbitrary literal marking.

Source application: Meierfrankenfeld--Stellmacher (1993), (5.5) and (5.12),
printed pp.915,924--927; the image-sixteen strict seed intersection uses
both covers and retains their full central attachment.
-/

public section
open Subgroup BinaryPermutation Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.StrictCubeInvariant
private abbrev M := Fin 6 → ZMod 2
private def pair45 : M := ![0,0,0,0,1,1]
private def actor (i : Fin 2) : Equiv.Perm (Fin 6) := ![swap01,swap23] i
private def word (x : M) (i : Fin 2) (b : Fin 4 → ZMod 2) : M :=
  b 0 • (fun _ => 1) + b 1 • pair45 + b 2 • x + b 3 • representation (Fin 6) (actor i) x
private abbrev paired (x : M) : Prop := x 0 = x 1 ∧ x 2 = x 3 ∧ x 4 = x 5
set_option maxRecDepth 3000 in
private theorem independent_certificate : ∀ x : M,
    (∑ i, x i) = 0 → ¬ paired x →
    ∃ i : Fin 2, Function.Injective (word x i) := by
  decide +kernel

private def oneCore : core (Fin 6) := ⟨fun _ => 1,by rw [mem_core]; decide⟩
private def pairCore : core (Fin 6) := ⟨pair45,by rw [mem_core]; decide⟩
private def wordCore (x : core (Fin 6)) (i : Fin 2) (b : Fin 4 → ZMod 2) : core (Fin 6) :=
  b 0 • oneCore + b 1 • pairCore + b 2 • x + b 3 • coreRepresentation (Fin 6) (actor i) x

private theorem pairCore_fixed (R : Subgroup (Equiv.Perm (Fin 6))) (hR : R ≤ H1) :
    pairCore ∈ fixedSpace (coreRepresentation (Fin 6)) R := by
  rintro ⟨g,hg⟩
  apply Subtype.ext
  funext i
  have hg' := mem_H1_cases (hR (R.inv_mem hg))
  change pair45 (g⁻¹ i) = pair45 i
  have hcert : ∀ j k : Fin 6,
      (k = 4 ↔ j = 4) ∧ (k = 5 ↔ j = 5) ∨
      (k = 4 ↔ j = 5) ∧ (k = 5 ↔ j = 4) → pair45 k = pair45 j := by decide
  apply hcert
  rcases hg' with ⟨h4,h5⟩ | ⟨h4,h5⟩
  · left
    exact ⟨by simpa only [h4] using (g⁻¹.injective.eq_iff (a := i) (b := 4)),
      by simpa only [h5] using (g⁻¹.injective.eq_iff (a := i) (b := 5))⟩
  · right
    exact ⟨by simpa only [h5] using (g⁻¹.injective.eq_iff (a := i) (b := 5)),
      by simpa only [h4] using (g⁻¹.injective.eq_iff (a := i) (b := 4))⟩

private theorem paired_fixed (x : core (Fin 6)) (hx : paired x.val) :
    x ∈ fixedSpace (coreRepresentation (Fin 6)) D := by
  rintro ⟨g,hg⟩
  change coreRepresentation (Fin 6) g x = x
  change g ∈ closure {swap01,swap23,swap45} at hg
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    have hcert : ∀ x : M, paired x →
        representation (Fin 6) swap01 x = x ∧ representation (Fin 6) swap23 x = x ∧
          representation (Fin 6) swap45 x = x := by decide +kernel
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Subtype.ext (hcert x.val hx).1
    · exact Subtype.ext (hcert x.val hx).2.1
    · exact Subtype.ext (hcert x.val hx).2.2
  | one => rfl
  | mul a b _ _ ha hb => rw [map_mul,Module.End.mul_apply,hb,ha]
  | inv a _ ha =>
    have hh := congrArg (coreRepresentation (Fin 6) a⁻¹) ha
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh.symm

/-- A strict invariant subspace between the duad fixed space and the core
is fixed by the full cube. -/
theorem core_le_fixed (R : Subgroup (Equiv.Perm (Fin 6))) (hDR : D ≤ R) (hR : R ≤ H1)
    (W : Submodule (ZMod 2) (core (Fin 6)))
    (hsmall : Nat.card W < 16)
    (hfixed : fixedSpace (coreRepresentation (Fin 6)) R ≤ W)
    (hinv : ∀ r ∈ R, ∀ x ∈ W, coreRepresentation (Fin 6) r x ∈ W) :
    W ≤ fixedSpace (coreRepresentation (Fin 6)) D := by
  intro x hx
  apply paired_fixed
  by_contra hn
  obtain ⟨i,hi⟩ := independent_certificate x.val ((mem_core (Fin 6) x.val).mp x.property) hn
  have hone : oneCore ∈ W := hfixed (fun _ => rfl)
  have hpair : pairCore ∈ W := hfixed (pairCore_fixed R hR)
  have hai : actor i ∈ R := hDR (by
    fin_cases i <;> exact subset_closure (by simp [actor]))
  have hw (b : Fin 4 → ZMod 2) : wordCore x i b ∈ W :=
    W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ hone) (W.smul_mem _ hpair))
      (W.smul_mem _ hx)) (W.smul_mem _ (hinv _ hai x hx))
  let f : (Fin 4 → ZMod 2) → W := fun b => ⟨wordCore x i b,hw b⟩
  have hf : Function.Injective f := by
    intro b c he
    apply hi
    exact congrArg (fun y : W => y.val.val) he
  have hcard := Nat.card_le_card_of_injective f hf
  norm_num only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,ZMod.card] at hcard
  omega


/-- The same strict cube-fixedness on the four-dimensional natural quotient. -/
theorem natural_le_fixed (R : Subgroup (Equiv.Perm (Fin 6))) (hDR : D ≤ R) (hR : R ≤ H1)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hsmall : Nat.card W < 8)
    (hfixed : fixedSpace (naturalRepresentation (Fin 6)) R ≤ W)
    (hinv : ∀ r ∈ R, ∀ x ∈ W, naturalRepresentation (Fin 6) r x ∈ W) :
    W ≤ fixedSpace (naturalRepresentation (Fin 6)) D := by
  let q := coreToNatural (Fin 6)
  let W₀ := W.comap q
  have hq : Function.Surjective q := coreToNatural_surjective
  have hker : q.ker ≤ W₀ := by
    intro x hx
    change q x ∈ W
    rw [LinearMap.mem_ker.mp hx]
    exact W.zero_mem
  have hkd : Module.finrank (ZMod 2) q.ker = 1 := by
    have hh := q.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hq,finrank_top,
      finrank_natural_even (Fin 6) (by decide),finrank_core] at hh
    norm_num only [Fintype.card_fin] at hh
    omega
  have hWmap : W₀.map q = W := Submodule.map_comap_eq_of_surjective hq W
  have hdim := (q.domRestrict W₀).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hker).finrank_eq,hkd,hWmap] at hdim
  have hcard : Nat.card W₀ < 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hsmall ⊢
    rw [←hdim,pow_succ]
    omega
  have hfix₀ : fixedSpace (coreRepresentation (Fin 6)) R ≤ W₀ := by
    intro x hx
    apply hfixed
    intro r
    exact (coreToNatural_equivariant r.val x).symm.trans (congrArg q (hx r))
  have hinv₀ : ∀ r ∈ R, ∀ x ∈ W₀, coreRepresentation (Fin 6) r x ∈ W₀ := by
    intro r hr x hx
    change q (coreRepresentation (Fin 6) r x) ∈ W
    rw [coreToNatural_equivariant]
    exact hinv r hr (q x) hx
  have hW₀ := core_le_fixed R hDR hR W₀ hcard hfix₀ hinv₀
  intro x hx r
  obtain ⟨y,rfl⟩ := hq x
  exact (coreToNatural_equivariant r.val y).symm.trans (congrArg q (hW₀ hx r))

private theorem conjugate_fixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (R D : Subgroup (Equiv.Perm (Fin 6))) (n : ℕ)
    (hbase : ∀ W : Submodule (ZMod 2) V, Nat.card W < n →
      fixedSpace ρ R ≤ W → (∀ r ∈ R, ∀ x ∈ W, ρ r x ∈ W) → W ≤ fixedSpace ρ D)
    (u : Equiv.Perm (Fin 6)) (W : Submodule (ZMod 2) V)
    (hsmall : Nat.card W < n)
    (hfixed : fixedSpace ρ (R.map (MulAut.conj u).toMonoidHom) ≤ W)
    (hinv : ∀ r ∈ R.map (MulAut.conj u).toMonoidHom, ∀ x ∈ W, ρ r x ∈ W) :
    W ≤ fixedSpace ρ (D.map (MulAut.conj u).toMonoidHom) := by
  have hleft (x : V) : ρ u⁻¹ (ρ u x) = x := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hright (x : V) : ρ u (ρ u⁻¹ x) = x := by
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  let W₀ := W.comap (ρ u)
  have hcard : Nat.card W₀ < n := by
    let f : W₀ → W := fun x => ⟨ρ u x.val,x.property⟩
    have hf : Function.Injective f := by
      intro x y he
      apply Subtype.ext
      have hh := congrArg (fun z : W => ρ u⁻¹ z.val) he
      simpa only [f,hleft] using hh
    exact (Nat.card_le_card_of_injective f hf).trans_lt hsmall
  have hfix₀ : fixedSpace ρ R ≤ W₀ := by
    intro x hx
    apply hfixed
    rintro ⟨r,hr⟩
    obtain ⟨a,ha,rfl⟩ := hr
    change ρ (u*a*u⁻¹) (ρ u x) = ρ u x
    rw [map_mul,map_mul]
    have haFix : ρ a x = x := hx ⟨a,ha⟩
    simp only [Module.End.mul_apply,hleft,haFix]
  have hinv₀ : ∀ r ∈ R, ∀ x ∈ W₀, ρ r x ∈ W₀ := by
    intro r hr x hx
    have hh := hinv ((MulAut.conj u) r) (mem_map_of_mem (MulAut.conj u).toMonoidHom hr)
      (ρ u x) hx
    change ρ (u*r*u⁻¹) (ρ u x) ∈ W at hh
    rw [map_mul,map_mul] at hh
    change ρ u (ρ r x) ∈ W
    simpa only [Module.End.mul_apply,hleft] using hh
  have hW₀ := hbase W₀ hcard hfix₀ hinv₀
  intro x hx
  rintro ⟨r,hr⟩
  obtain ⟨a,ha,rfl⟩ := hr
  have hx₀ : ρ u⁻¹ x ∈ W₀ := by change ρ u (ρ u⁻¹ x) ∈ W; rwa [hright]
  have hh := congrArg (ρ u) (hW₀ hx₀ ⟨a,ha⟩)
  change ρ u (ρ a (ρ u⁻¹ x)) = ρ u (ρ u⁻¹ x) at hh
  change ρ (u*a*u⁻¹) x = x
  rw [map_mul,map_mul]
  simpa only [Module.End.mul_apply,hright] using hh

/-- Strict core intersections are fixed by the cube in the same marking. -/
theorem core_conjugate_le_fixed (R : Subgroup (Equiv.Perm (Fin 6)))
    (hDR : D ≤ R) (hR : R ≤ H1) (u : Equiv.Perm (Fin 6))
    (W : Submodule (ZMod 2) (core (Fin 6))) (hsmall : Nat.card W < 16)
    (hfixed : fixedSpace (coreRepresentation (Fin 6)) (R.map (MulAut.conj u).toMonoidHom) ≤ W)
    (hinv : ∀ r ∈ R.map (MulAut.conj u).toMonoidHom, ∀ x ∈ W,
      coreRepresentation (Fin 6) r x ∈ W) :
    W ≤ fixedSpace (coreRepresentation (Fin 6)) (D.map (MulAut.conj u).toMonoidHom) :=
  conjugate_fixed (coreRepresentation (Fin 6)) R D 16 (core_le_fixed R hDR hR) u W hsmall hfixed hinv

/-- Strict natural intersections are fixed by the cube in the same marking. -/
theorem natural_conjugate_le_fixed (R : Subgroup (Equiv.Perm (Fin 6)))
    (hDR : D ≤ R) (hR : R ≤ H1) (u : Equiv.Perm (Fin 6))
    (W : Submodule (ZMod 2) (natural (Fin 6))) (hsmall : Nat.card W < 8)
    (hfixed : fixedSpace (naturalRepresentation (Fin 6)) (R.map (MulAut.conj u).toMonoidHom) ≤ W)
    (hinv : ∀ r ∈ R.map (MulAut.conj u).toMonoidHom, ∀ x ∈ W,
      naturalRepresentation (Fin 6) r x ∈ W) :
    W ≤ fixedSpace (naturalRepresentation (Fin 6)) (D.map (MulAut.conj u).toMonoidHom) :=
  conjugate_fixed (naturalRepresentation (Fin 6)) R D 8 (natural_le_fixed R hDR hR) u W hsmall hfixed hinv

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.StrictCubeInvariant
