module

public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquareData
public import Theory.ElementaryAbelian.BinaryExpansion

/-!
# Faithful finite coordinates for the normalizer square calculation

The five supplied elementary generators span all 32 binary tails. Their
number and the order of F give unique tail coordinates. The assumed
injectivity of the F-valued normalizer words then gives faithful finite
coordinates, and equality of their heads detects equality of F-cosets.

The only omega test needed by the finite square certificate is one-way:
if both the x and c exponents are even, the word commutes with v and lies
in omega. This follows directly from x² = yz, c² = wu and b² = v.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph, using equations (1)–(19).
-/
open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.ParrottNormalizerRootSquare
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem tailWord_surjective (f : ParrottSylowGeneratorData n) :
    Function.Surjective (fun q : Fin 8 × Fin 4 => (⟨tailWord f q, tailWord_mem f q⟩ : e.F)) := by
  let _ := e.elementary
  let A : e.F := ⟨f.a, f.elementary_basis ▸ subset_closure (by simp)⟩
  let U : e.F := ⟨f.u, f.elementary_basis ▸ subset_closure (by simp)⟩
  let V : e.F := ⟨n.v, n.v_mem_inf.2⟩
  let T : e.F := ⟨n.t, n.t_mem_inf.2⟩
  let Z : e.F := ⟨z, e.z_mem_inf.2⟩
  let basis : Fin 5 → e.F := ![A,U,V,T,Z]
  have hcl : closure (Set.range basis) = ⊤ := by
    apply Subgroup.map_injective e.F.subtype_injective
    rw [MonoidHom.map_closure]
    have himg : e.F.subtype '' Set.range basis = ({z,n.t,n.v,f.u,f.a} : Set G) := by
      simp [basis, Matrix.range_cons, Set.image_insert_eq, A,U,V,T,Z]
    rw [himg, f.elementary_basis, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro q
  obtain ⟨b,hb⟩ := Theory.GroupTheory.exists_bool_prod_of_mem_closure_range basis
    (fun i => by
      apply Subtype.ext
      exact (pow_two (basis i : G)).symm.trans
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (basis i : G) (basis i).property))
    (show q ∈ closure (Set.range basis) by rw [hcl]; trivial)
  have hb' : q = (if b 0 then A else 1) * (if b 1 then U else 1) *
      (if b 2 then V else 1) * (if b 3 then T else 1) * (if b 4 then Z else 1) := by
    simpa [Fin.prod_univ_succ, basis, mul_assoc] using hb
  refine ⟨(⟨(b 0).toNat + 2 * (b 1).toNat + 4 * (b 2).toNat, ?_⟩,
    ⟨(b 3).toNat + 2 * (b 4).toNat, ?_⟩), ?_⟩
  · cases b 0 <;> cases b 1 <;> cases b 2 <;> decide
  · cases b 3 <;> cases b 4 <;> decide
  · apply Subtype.ext
    have hh := congrArg Subtype.val hb'
    cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
      cases h3 : b 3 <;> cases h4 : b 4 <;>
      simpa [tailWord, h0,h1,h2,h3,h4,A,U,V,T,Z] using hh.symm

private theorem tailWord_injective (f : ParrottSylowGeneratorData n) :
    Function.Injective (tailWord f) := by
  have hh := (tailWord_surjective f).bijective_of_nat_card_le (by
    simp only [Nat.card_prod, Nat.card_fin, e.card]; omega)
  intro p q hpq
  exact hh.1 (Subtype.ext hpq)

private def head (h : Fin 32) : Fin 4 × Fin 4 × Fin 2 :=
    (⟨h.val % 4, Nat.mod_lt _ (by decide)⟩,
     ⟨h.val / 4 % 4, Nat.mod_lt _ (by decide)⟩,
     ⟨h.val / 16, by omega⟩)

private theorem head_injective : Function.Injective head := by
  intro p q hpq
  have hi := congrArg (fun h => h.1.val) hpq
  have hj := congrArg (fun h => h.2.1.val) hpq
  have hk := congrArg (fun h => h.2.2.val) hpq
  simp only [head] at hi hj hk
  apply Fin.ext
  omega

private theorem head_surjective : Function.Surjective head := by
  rintro ⟨i,j,k⟩
  refine ⟨⟨i.val + 4*j.val + 16*k.val, by omega⟩, ?_⟩
  apply Prod.ext
  · apply Fin.ext; simp only [head]; omega
  · apply Prod.ext <;> apply Fin.ext <;> simp only [head] <;> omega

private def parameters (f : ParrottSylowGeneratorData n) (p : Code) : f.NormalizerRootParameters :=
   ((head p.1).1, (head p.1).2.1, (head p.1).2.2,
     ⟨tailWord f p.2, tailWord_mem f p.2⟩)

private theorem parameters_injective (f : ParrottSylowGeneratorData n) :
     Function.Injective (parameters f) := by
   intro p q hpq
   apply Prod.ext
   · apply head_injective
     exact congrArg (fun t => (t.1,t.2.1,t.2.2.1)) hpq
   · apply tailWord_injective f
     exact congrArg (fun t => (t.2.2.2 : G)) hpq

private theorem parameters_surjective (f : ParrottSylowGeneratorData n) :
     Function.Surjective (parameters f) := by
   rintro ⟨i,j,k,q⟩
   obtain ⟨h,hh⟩ := head_surjective (i,j,k)
   obtain ⟨t,ht⟩ := tailWord_surjective f q
   refine ⟨(h,t), ?_⟩
   simp only [parameters, hh, ht]

private theorem word_eq (f : ParrottSylowGeneratorData n) (p : Code) :
     word f p = f.normalizerRootWord (parameters f p) := rfl

/-- The finite encoding inherits faithful elementary cosets from word injectivity. -/
public theorem coordinateLaws (f : ParrottSylowGeneratorData n)
     (hinj : Function.Injective f.normalizerRootWord) : CoordinateLaws f := by
   have hc : ∀ p q : Code, (word f p)⁻¹ * word f q ∈ e.F ↔ p.1 = q.1 := by
     intro p q
     constructor
     · intro hpq
       let d : e.F := ⟨(word f p)⁻¹ * word f q, hpq⟩
       let r : f.NormalizerRootParameters :=
         ((head p.1).1, (head p.1).2.1, (head p.1).2.2,
           (parameters f p).2.2.2 * d)
       have hr : f.normalizerRootWord r = f.normalizerRootWord (parameters f q) := by
         change _ * _ * _ * (tailWord f p.2 * ((word f p)⁻¹ * word f q)) = word f q
         rw [← mul_assoc]
         change word f p * ((word f p)⁻¹ * word f q) = word f q
         simp
       have heq := hinj hr
       apply head_injective
       exact congrArg (fun t => (t.1,t.2.1,t.2.2.1)) heq
     · intro hpq
       have heq : (word f p)⁻¹ * word f q = (tailWord f p.2)⁻¹ * tailWord f q.2 := by
         simp only [word, hpq]
         group
       rw [heq]
       exact e.F.mul_mem (e.F.inv_mem (tailWord_mem f _)) (tailWord_mem f _)
   refine ⟨?_, ?_, ?_, hc⟩
   · exact hinj.comp (parameters_injective f)
   · ext g
     constructor
     · rintro ⟨p,rfl⟩; exact ⟨parameters f p,rfl⟩
     · rintro ⟨q,rfl⟩
       obtain ⟨p,rfl⟩ := parameters_surjective f q
       exact ⟨p,rfl⟩
   · intro p
     have hh := hc (0,0,0) p
     simpa only [word_zero, inv_one, one_mul, eq_comm] using hh

/-- A word outside omega has an odd x or c exponent. -/
public theorem outside_omega (f : ParrottSylowGeneratorData n) (p : Code)
     (hp : word f p ∉ (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
       ((normalizer (e.F : Set G)).subtype.comp
         (pCore 2 (normalizer (e.F : Set G))).subtype)) : outside p.1 := by
   let _ := e.elementary
   by_contra hh
   apply hp
   apply (f.normalizer_core_mem_omega_iff_commute_v (word f p)
     (f.normalizerRootWord_mem_core (parameters f p))).mpr
   have htail : Commute (tailWord f p.2) n.v := congrArg e.F.subtype
     (mul_comm (⟨_, tailWord_mem f p.2⟩ : e.F) ⟨n.v,n.v_mem_inf.2⟩)
   have hy : Commute f.y n.v := by
     have hv := f.y_conjugation.1
     change f.y⁻¹ * n.v * f.y⁻¹⁻¹ = n.v at hv
     rw [inv_inv] at hv
     show f.y * n.v = n.v * f.y
     calc
       f.y * n.v = f.y * (f.y⁻¹ * n.v * f.y) := by rw [hv]
       _ = n.v * f.y := by group
   have hx2 : Commute (f.x ^ 2) n.v := by
     rw [f.eq04]; exact hy.mul_left f.comm_zv
   have hc2 : Commute (f.c ^ 2) n.v := by
     rw [f.eq13]; exact f.comm_vw.symm.mul_left f.comm_vu.symm
   have hb : Commute f.b n.v := by
     rw [← f.eq03_b]; exact Commute.self_pow _ _
   apply Commute.mul_left _ htail
   apply Commute.mul_left _ (hb.pow_left _)
   rcases p with ⟨h,r,c⟩
   fin_cases h <;> norm_num [outside] at hh
   all_goals norm_num
   all_goals first | exact hx2.mul_left hc2 | exact hx2 | exact hc2
end Stellmacher.Recognition.ParrottNormalizerRootSquare
