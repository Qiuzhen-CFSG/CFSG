module

public import Stellmacher.Recognition.Parrott.LocalGeneratorData
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# A reduced candidate for Parrott's normalizer generator

The square-root orbit argument on pp.681–682 selects an involution normalizing
F whose actions on t,v,y are fixed and whose actions on a,x have two remaining
possibilities. `ParrottNormalizerSeedData` records precisely this intermediate
output, without asserting that it exists. The subsequent calculation excludes
xˢ=caw and determines equations (25)–(26).

The support results below discharge the subgroup and fusion parts of the final
construction. An element moving t to z generates N together with T, because
[N:T]=3. The word dvz is conjugate to d by bt, and d is in J outside J′; thus
(sd vz)³=1 places s in the class of v by the odd-product involution argument.
Neither result requires the braid equation or a choice of new Sylow coordinates.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed pp.681–682, “Generators and relations for N”.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}


/-- The output of the square-root orbit selection, before exclusion of the
wrong x-image. Every coordinate is that of the supplied centralizer frame. -/
public structure ParrottNormalizerSeedData (f : ParrottCentralizerGeneratorData n) where
  s : G
  mem_normalizer : s ∈ normalizer (e.F : Set G)
  sq : s ^ 2 = 1
  t_conj : s⁻¹ * n.t * s = z
  v_conj : s⁻¹ * n.v * s = n.v * n.t * z
  y_conj : s⁻¹ * f.y * s = f.w * f.u * n.v * z
  a_conj : s⁻¹ * f.a * s = f.u ∨ s⁻¹ * f.a * s = f.u * z
  x_conj : s⁻¹ * f.x * s = f.c * f.a * f.w ∨
    s⁻¹ * f.x * s = f.c * f.a * f.w * n.t * z

/-- Moving t to z forces generation of the actual normalizer together with T.
No order assumption on the moving element is needed. -/
public theorem ParrottNormalizerFusionData.normalizer_generated_of_t_conjugate
    (n : ParrottNormalizerFusionData e) [Finite G] (h : ParrottCentralizerHypotheses z)
    (s : G) (hsN : s ∈ normalizer (e.F : Set G))
    (hts : s⁻¹ * n.t * s = z) :
    (e.sylow : Subgroup G) ⊔ zpowers s = normalizer (e.F : Set G) := by
  have htne : n.t ≠ z := fun ht => n.t_not_mem_zpowers (by rw [ht]; exact mem_zpowers z)
  have hsT : s ∉ e.sylow := by
    intro hsT
    have hsz := mem_centralizer_singleton_iff.mp (e.sylow_le_centralizer hsT)
    apply htne
    calc
      n.t = s * (s⁻¹ * n.t * s) * s⁻¹ := by group
      _ = s * z * s⁻¹ := by rw [hts]
      _ = z := by rw [hsz]; group
  let L : Subgroup G := (e.sylow : Subgroup G) ⊔ zpowers s
  have hTL : (e.sylow : Subgroup G) ≤ L := le_sup_left
  have hLN : L ≤ normalizer (e.F : Set G) :=
    sup_le e.sylow_le_normalizer (zpowers_le.mpr hsN)
  have hTN : (e.sylow : Subgroup G).relIndex (normalizer (e.F : Set G)) = 3 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (e.sylow : Subgroup G)
      (normalizer (e.F : Set G)) bot_le e.sylow_le_normalizer
    rw [relIndex_bot_left, relIndex_bot_left, e.sylow_card h, n.normalizer_card] at hc
    omega
  have hmul := relIndex_mul_relIndex (e.sylow : Subgroup G) L
    (normalizer (e.F : Set G)) hTL hLN
  rw [hTN] at hmul
  have hnotone : (e.sylow : Subgroup G).relIndex L ≠ 1 := by
    intro heq
    exact hsT ((relIndex_eq_one.mp heq) (mem_sup_right (mem_zpowers s)))
  have hidx : (e.sylow : Subgroup G).relIndex L = 3 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp ⟨_, hmul.symm⟩).resolve_left hnotone
  have hLNidx : L.relIndex (normalizer (e.F : Set G)) = 1 := by
    rw [hidx] at hmul
    omega
  exact le_antisymm hLN (relIndex_eq_one.mp hLNidx)

variable (f : ParrottSylowGeneratorData n)
/-- The normalized generator d lies in the second involution class. -/
public theorem ParrottSylowGeneratorData.d_isConj_v [Finite G] (h : ParrottCentralizerHypotheses z) : IsConj f.d n.v := by
  have hz1 : z ≠ 1 := by intro hz; simpa [hz] using h.involution
  have hdJ : f.d ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
    rw [← f.core_generators]
    exact subset_closure (by simp)
  have hdnE : f.d ∉ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) := by
    intro hdE
    have hc := mem_centralizer_singleton_iff.mp
      ((e.derived_le_t_centralizer h n.t n.t_mem_inf.1 hdE).2)
    have heq : Tits.parrottCommutator f.d n.t = 1 :=
      (Tits.parrottCommutator_eq_one_iff _ _).mpr hc
    exact hz1 (f.eq03_dt.symm.trans heq)
  have hdne : f.d ≠ 1 := by
    intro hd
    exact hdnE (hd ▸ one_mem _)
  have hd2 : orderOf f.d = 2 := orderOf_eq_prime_iff.mpr ⟨f.d_sq, hdne⟩
  obtain ⟨l, hl⟩ := n.original_core_fusion f.d hdJ hdnE hd2
  exact (isConj_iff.mpr ⟨(l : G), hl⟩).symm

/-- Conjugation by bt sends d to the exact word occurring in equation (26). -/
public theorem ParrottSylowGeneratorData.dvz_conjugate_eq :
    (f.b * n.t)⁻¹ * f.d * (f.b * n.t) = f.d * n.v * z := by
  have db := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_db
  have dt := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_dt
  have db' : f.b⁻¹ * f.d * f.b = f.d * n.v := by
    calc
      _ = f.b⁻¹ * (f.d * f.b) := by group
      _ = f.d * n.v := by rw [db]; group
  calc
    _ = n.t⁻¹ * (f.b⁻¹ * f.d * f.b) * n.t := by group
    _ = n.t⁻¹ * (f.d * n.v) * n.t := by rw [db']
    _ = n.t⁻¹ * (f.d * n.t) * n.v := by rw [mul_assoc, mul_assoc, f.comm_tv.symm.eq]; group
    _ = f.d * n.v * z := by rw [dt]; simp only [mul_assoc, inv_mul_cancel_left]; rw [f.comm_zv.eq]

/-- The cubic relation supplies the required involution class for s. -/
public theorem ParrottSylowGeneratorData.isConj_v_of_cube [Finite G] (h : ParrottCentralizerHypotheses z)
    (s : G) (hs : s ^ 2 = 1) (hcube : (s * f.d * n.v * z) ^ 3 = 1) :
    IsConj s n.v := by
  have hdvz : IsConj f.d (f.d * n.v * z) :=
    isConj_iff.mpr ⟨(f.b * n.t)⁻¹, by simpa only [inv_inv] using f.dvz_conjugate_eq⟩
  have hdvz2 : (f.d * n.v * z) ^ 2 = 1 := by
    rw [← f.dvz_conjugate_eq]
    have hc := congrArg (fun g : G => (f.b * n.t)⁻¹ * g * (f.b * n.t)) f.d_sq
    convert hc using 1 <;> simp only [pow_two, mul_one] <;> group
  have hodd : Odd (orderOf (s * (f.d * n.v * z))) :=
    (by decide : Odd 3).of_dvd_nat
      (orderOf_dvd_of_pow_eq_one (by simpa only [mul_assoc] using hcube))
  exact (isConj_of_involutions_odd_product s _ hs hdvz2 hodd).trans
    (hdvz.symm.trans (f.d_isConj_v h))
end Stellmacher.Recognition
