module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.Overgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The order-32 group in Held's lambda argument

The source subgroup W = S⟨mu′xi⟩ is the common local centralizer of lambda
and pi*lambda. Its center E = ⟨pi,mu,lambda⟩ has order eight, and the full
ambient centralizer of E is W. The center has three generators, as printed
in Held's Lemma 2.4; omitting mu changes the statement.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, printed p.226.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates

/-- Held's W = S⟨mu′xi⟩, in the concrete centralizer model. -/
public abbrev lambdaModelCore : Subgroup H := sCaseCentralizer 1

/-- The center of W, as a subgroup of the concrete model H. -/
@[expose] public def lambdaModelCenter : Subgroup H :=
  modelS ⊓ centralizer ({mup * xi} : Set H)

public theorem lambdaModelCore_eq :
    lambdaModelCore = modelS ⊔ zpowers (mup * xi) := sCaseCentralizer_eq_sup 1

public theorem lambdaModelCore_card : Nat.card lambdaModelCore = 32 :=
  sCaseCentralizer_card 1

public theorem lambdaModelCore_eq_centralizer_lam :
    lambdaModelCore = centralizer ({lam} : Set H) := by
  ext x
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  change x * (pi * lam) = pi * lam * x ↔ x * lam = lam * x
  have hp := mem_center_iff.mp modelCentralInvolution_mem_center x
  change x * pi = pi * x at hp
  rw [← mul_assoc, hp, mul_assoc, mul_assoc, mul_left_cancel_iff]

public theorem lambdaModelCenter_le_core : lambdaModelCenter ≤ lambdaModelCore :=
  inf_le_left.trans (modelS_le_sCaseCentralizer 1)

public theorem lambdaModelCore_centralizer :
    centralizer (lambdaModelCore : Set H) = lambdaModelCenter := by
  apply le_antisymm
  · intro x hx
    refine ⟨?_, ?_⟩
    · change x ∈ elementary 1
      rw [← elementary_selfCentralizing 1]
      exact centralizer_le (modelS_le_sCaseCentralizer 1) hx
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx (mup * xi) (sCaseExtra_mem 1)).symm
  · intro x hx
    apply mem_centralizer_iff.mpr
    have hs : modelS ≤ centralizer ({x} : Set H) := by
      intro y hy
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp ((elementary_selfCentralizing 1).symm ▸ hx.1) y hy)
    have hq : zpowers (mup * xi) ≤ centralizer ({x} : Set H) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hx.2).symm)
    intro y hy
    exact mem_centralizer_singleton_iff.mp
      ((sup_le hs hq) (lambdaModelCore_eq ▸ hy))

public theorem lambdaModelCenter_pi : pi ∈ lambdaModelCenter :=
  ⟨pi_mem_elementary 1, mem_centralizer_singleton_iff.mpr (by decide +kernel)⟩

public theorem lambdaModelCenter_mu : mu ∈ lambdaModelCenter :=
  ⟨mu_mem_elementary 1, mem_centralizer_singleton_iff.mpr (by decide +kernel)⟩

public theorem lambdaModelCenter_lam : lam ∈ lambdaModelCenter :=
  ⟨elementaryGenerators_mem 1 3, mem_centralizer_singleton_iff.mpr (by decide +kernel)⟩

public theorem lambdaModelCenter_centralizer :
    centralizer (lambdaModelCenter : Set H) = lambdaModelCore := by
  apply le_antisymm
  · intro x hx
    rw [lambdaModelCore_eq_centralizer_lam]
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx lam lambdaModelCenter_lam).symm
  · intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [← lambdaModelCore_centralizer] at hy
    exact (mem_centralizer_iff.mp hy x hx).symm

private abbrev CenterCode := Fin 2 × Fin 2 × Fin 2
private def centerWord (a : CenterCode) : H := elementaryWord 1 (a.1, a.2.1, 0, a.2.2)
private def centerLift (a : CenterCode) : lambdaModelCenter :=
  ⟨centerWord a, ⟨(mem_elementary 1 _).mpr ⟨(a.1, a.2.1, 0, a.2.2), rfl⟩,
    mem_centralizer_singleton_iff.mpr (by
      have ht : ∀ a : CenterCode, centerWord a * (mup * xi) = (mup * xi) * centerWord a := by
        decide +kernel
      exact ht a)⟩⟩

private theorem centerLift_bijective : Function.Bijective centerLift := by
  constructor
  · intro a b hab
    have hv : centerWord a = centerWord b := congrArg Subtype.val hab
    simp only [centerWord, elementaryWord_eq_word] at hv
    have h := word_injective hv
    simpa [elementaryCode, Prod.ext_iff, and_assoc] using h
  · rintro ⟨x, hxS, hxq⟩
    obtain ⟨b, rfl⟩ := (mem_elementary 1 x).mp hxS
    have ht : ∀ b : BaseCode,
        elementaryWord 1 b * (mup * xi) = (mup * xi) * elementaryWord 1 b → b.2.2.1 = 0 := by
      decide +kernel
    have hb := ht b (mem_centralizer_singleton_iff.mp hxq)
    refine ⟨(b.1, b.2.1, b.2.2.2), Subtype.ext ?_⟩
    change elementaryWord 1 (b.1, b.2.1, 0, b.2.2.2) = elementaryWord 1 b
    congr 1
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext hb.symm rfl))

public theorem lambdaModelCenter_card : Nat.card lambdaModelCenter = 8 := by
  rw [← Nat.card_congr (Equiv.ofBijective centerLift centerLift_bijective)]
  simp [CenterCode]

public theorem lambdaModelCenter_elementary : IsElementaryAbelian 2 lambdaModelCenter := by
  let := elementary_isElementaryAbelian 1
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply Subtype.ext
    exact setLike_mul_comm (show (x : H) ∈ modelS from x.property.1)
      (show (y : H) ∈ modelS from y.property.1)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : H) x.property.1

/-- The source center has exactly the three generators pi, mu and lambda. -/
public theorem lambdaModelCenter_eq :
    lambdaModelCenter = closure ({pi, mu, lam} : Set H) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := centerLift_bijective.surjective ⟨x, hx⟩
    have he : centerWord a = x := congrArg Subtype.val ha
    rw [← he]
    change pi ^ a.1.val * mu ^ a.2.1.val * tau ^ 0 * lam ^ a.2.2.val ∈
      closure ({pi, mu, lam} : Set H)
    rw [pow_zero, mul_one]
    exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact lambdaModelCenter_pi
    · exact lambdaModelCenter_mu
    · exact lambdaModelCenter_lam

/-- The only nonidentity square in W is pi*mu. -/
public theorem lambdaModelCore_square_cases (x : lambdaModelCore) :
    (x : H) ^ 2 = 1 ∨ (x : H) ^ 2 = pi * mu := by
  obtain ⟨b, hb⟩ := word_bijective.surjective (x : H)
  have hx := mem_centralizer_singleton_iff.mp x.property
  rw [← hb] at hx ⊢
  have ht : ∀ b : Code, word b * (pi * lam) = (pi * lam) * word b →
      word b ^ 2 = 1 ∨ word b ^ 2 = pi * mu := by decide +kernel
  exact ht b hx

/-- Every automorphism of W fixes its unique nonidentity square. -/
public theorem lambdaModelCore_aut_fixes_pi_mu (a : MulAut lambdaModelCore) :
    a ⟨pi * mu, lambdaModelCenter_le_core
      (lambdaModelCenter.mul_mem lambdaModelCenter_pi lambdaModelCenter_mu)⟩ =
      ⟨pi * mu, lambdaModelCenter_le_core
        (lambdaModelCenter.mul_mem lambdaModelCenter_pi lambdaModelCenter_mu)⟩ := by
  let c : lambdaModelCore := ⟨pi * mu, lambdaModelCenter_le_core
    (lambdaModelCenter.mul_mem lambdaModelCenter_pi lambdaModelCenter_mu)⟩
  let r : lambdaModelCore := ⟨tau * (mup * xi), lambdaModelCore.mul_mem
    (modelS_le_sCaseCentralizer 1 (elementaryGenerators_mem 1 2)) (sCaseExtra_mem 1)⟩
  have hr : r ^ 2 = c := by apply Subtype.ext; decide +kernel
  have hn : c ≠ 1 := by
    intro h
    exact (show pi * mu ≠ (1 : H) by decide +kernel) (congrArg Subtype.val h)
  have hs := lambdaModelCore_square_cases (a r)
  change ((a r) ^ 2 : lambdaModelCore).val = 1 ∨
    ((a r) ^ 2 : lambdaModelCore).val = c.val at hs
  rw [← map_pow, hr] at hs
  rcases hs with h | h
  · exact (hn (a.injective (by simpa using (Subtype.ext h : a c = 1)))).elim
  · exact Subtype.ext h

/-- W has exactly two possible elementary subgroups of order sixteen. -/
public theorem lambdaModelCore_elementary_sixteen (A : Subgroup H)
    (hA : A ≤ lambdaModelCore) (he : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    A = modelS ∨ A = modelL1 := by
  obtain ⟨k, rfl⟩ := model_elementary_sixteen A
    (hA.trans (sCaseCentralizer_le_modelD 1)) he hc
  have ht (j : Fin 4) := mem_centralizer_singleton_iff.mp
    (hA (elementaryGenerators_mem k j))
  fin_cases k
  · exact (show elementaryGenerators 0 3 * (pi * lam) ≠
        (pi * lam) * elementaryGenerators 0 3 by decide +kernel) (ht 3) |>.elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (show elementaryGenerators 3 3 * (pi * lam) ≠
        (pi * lam) * elementaryGenerators 3 3 by decide +kernel) (ht 3) |>.elim

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The actual ambient W from Held's Lemma 2.4. -/
@[expose] public noncomputable def lambdaCore : Subgroup G :=
  lambdaModelCore.map (D.a10ModelEmbedding e)

/-- The actual ambient elementary center E of W. -/
@[expose] public noncomputable def lambdaCenter : Subgroup G :=
  lambdaModelCenter.map (D.a10ModelEmbedding e)

public theorem lambdaCore_card : Nat.card (lambdaCore D e) = 32 := by
  rw [lambdaCore, card_map_of_injective (D.a10ModelEmbedding_injective e), lambdaModelCore_card]

public theorem lambdaCenter_card : Nat.card (lambdaCenter D e) = 8 := by
  rw [lambdaCenter, card_map_of_injective (D.a10ModelEmbedding_injective e), lambdaModelCenter_card]

public theorem lambdaCenter_elementary : IsElementaryAbelian 2 (lambdaCenter D e) := by
  let := lambdaModelCenter_elementary
  exact IsElementaryAbelian.map (D.a10ModelEmbedding e)

public theorem lambdaCenter_le_core : lambdaCenter D e ≤ lambdaCore D e :=
  map_mono lambdaModelCenter_le_core

public theorem ambientS_le_lambdaCore : ambientElementary D e 1 ≤ lambdaCore D e :=
  ambientS_le_sCaseCentralizer D e 1

public theorem lambdaCenter_pi : D.a10ModelEmbedding e pi ∈ lambdaCenter D e :=
  mem_map_of_mem _ lambdaModelCenter_pi

public theorem lambdaCenter_mu : D.a10ModelEmbedding e mu ∈ lambdaCenter D e :=
  mem_map_of_mem _ lambdaModelCenter_mu

public theorem lambdaCenter_lam : D.a10ModelEmbedding e lam ∈ lambdaCenter D e :=
  mem_map_of_mem _ lambdaModelCenter_lam

private theorem centralizer_map_of_pi_mem [Finite G] (A : Subgroup H) (hp : pi ∈ A) :
    centralizer (A.map (D.a10ModelEmbedding e) : Set G) =
      (centralizer (A : Set H)).map (D.a10ModelEmbedding e) := by
  let f := D.a10ModelEmbedding e
  ext x
  constructor
  · intro hx
    have hxH : x ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      rw [← D.a10ModelEmbedding_central e]
      exact (mem_centralizer_iff.mp hx (f pi) (mem_map_of_mem f hp)).symm
    have hxr : x ∈ f.range := by rwa [D.a10ModelEmbedding_range e]
    obtain ⟨y, rfl⟩ := hxr
    refine ⟨y, mem_centralizer_iff.mpr ?_, rfl⟩
    intro t ht
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_iff.mp hx (f t) (mem_map_of_mem f ht)
  · rintro ⟨y, hy, rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨t, ht, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hy t ht)

public theorem lambdaCore_centralizer [Finite G] :
    centralizer (lambdaCore D e : Set G) = lambdaCenter D e := by
  rw [lambdaCore, centralizer_map_of_pi_mem D e _
    (lambdaModelCenter_le_core lambdaModelCenter_pi), lambdaModelCore_centralizer]
  rfl

public theorem lambdaCenter_centralizer [Finite G] :
    centralizer (lambdaCenter D e : Set G) = lambdaCore D e := by
  rw [lambdaCenter, centralizer_map_of_pi_mem D e _ lambdaModelCenter_pi,
    lambdaModelCenter_centralizer]
  rfl

/-- The normalizers of W and its center E coincide, since they centralize each other exactly. -/
public theorem lambdaCenter_normalizer_eq [Finite G] :
    normalizer (lambdaCenter D e : Set G) = normalizer (lambdaCore D e : Set G) := by
  apply le_antisymm
  · simpa only [lambdaCenter_centralizer] using
      normalizer_le_normalizer_centralizer (lambdaCenter D e)
  · simpa only [lambdaCore_centralizer] using
      normalizer_le_normalizer_centralizer (lambdaCore D e)

/-- W-normalizers centralize pi*mu, its unique nonidentity square. -/
public theorem lambdaCore_normalizer_le_centralizer [Finite G] :
    normalizer (lambdaCore D e : Set G) ≤
      centralizer ({D.a10ModelEmbedding e (pi * mu)} : Set G) := by
  intro g hg
  let b := (lambdaCore D e).normalizerMonoidHom ⟨g, hg⟩
  let c := lambdaModelCore.equivMapOfInjective (D.a10ModelEmbedding e)
    (D.a10ModelEmbedding_injective e)
  let a : MulAut lambdaModelCore := c.trans (b.trans c.symm)
  have he (y : lambdaModelCore) :
      D.a10ModelEmbedding e (a y : H) = g * D.a10ModelEmbedding e (y : H) * g⁻¹ :=
    congrArg Subtype.val (c.apply_symm_apply (b (c y)))
  have h := he ⟨pi * mu, lambdaModelCenter_le_core
    (lambdaModelCenter.mul_mem lambdaModelCenter_pi lambdaModelCenter_mu)⟩
  rw [lambdaModelCore_aut_fixes_pi_mu] at h
  exact mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp h.symm)

/-- The elementary sixteens in the actual W are precisely S and L₁. -/
public theorem lambdaCore_elementary_sixteen [Finite G] (A : Subgroup G)
    (hA : A ≤ lambdaCore D e) (he : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    A = ambientElementary D e 1 ∨ A = ambientElementary D e 2 := by
  obtain ⟨k, rfl⟩ := ambient_elementary_sixteen D e A
    (hA.trans (ambientSCaseCentralizer_le_ambientD D e 1)) he hc
  have ht (j : Fin 4) : elementaryGenerators k j * (pi * lam) =
      (pi * lam) * elementaryGenerators k j := by
    have hm := hA (mem_map_of_mem (D.a10ModelEmbedding e) (elementaryGenerators_mem k j))
    obtain ⟨y, hy, hyf⟩ := hm
    have hy' : y = elementaryGenerators k j := D.a10ModelEmbedding_injective e hyf
    subst y
    exact mem_centralizer_singleton_iff.mp hy
  fin_cases k
  · exact (show elementaryGenerators 0 3 * (pi * lam) ≠
        (pi * lam) * elementaryGenerators 0 3 by decide +kernel) (ht 3) |>.elim
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (show elementaryGenerators 3 3 * (pi * lam) ≠
        (pi * lam) * elementaryGenerators 3 3 by decide +kernel) (ht 3) |>.elim

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
