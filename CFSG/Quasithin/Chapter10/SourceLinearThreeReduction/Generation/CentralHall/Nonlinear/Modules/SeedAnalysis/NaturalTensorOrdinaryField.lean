module
public import Theory.SpecificGroups.SL2.BorelHallFieldAction
public import Theory.SpecificGroups.Suzuki.BorelPreserverFieldAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorInverseField

/-!
# Ordinary field action on the original central Hall subgroup

For a normal binary linear or Suzuki source component of the original H,
its actual Borel quotient character identifies the prescribed odd Hall B
with the field units. Conjugation by the same Sylow exchanger is therefore
ordinary field action. The natural-tensor Cartan computes inverse field
action on this very B, and the established incompatibility excludes both
normal rank-one rows. Hall arithmetic identifies the model degree without
asserting equality of generation parameters across a solvable kernel.

Source: Aschbacher--Smith, 9.2.7, pp.731--732, used in the centralizing-Z
branch of 10.2.3, p.745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.SpecialLinearGroup

variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
/-- Restriction to the original Hall subgroup of a normal marked Borel. -/
theorem normal_borel_hall_field_action (S : Sylow 2 X) (M K B : Subgroup X)
    [K.Normal] (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hSM : (S : Subgroup X) ≤ M) (hBM : B ≤ M)
    (hHall : IsHallSubgroup OddHall.oddPrimes (B.subgroupOf M))
    (ho : Odd (Nat.card B))
    {Y : Type*} [Group Y] (U : Subgroup Y)
    (π : U →* Fˣ) (hπ : Function.Surjective π)
    (hfield : ∀ (α : MulAut Y) (hα : ∀ x ∈ U, α x ∈ U),
      ∃ σ : F ≃+* F, ∀ x : U, π ⟨α x,hα x x.property⟩ =
        Units.map σ.toMonoidHom (π x))
    (e : sourceImage M K ≃* Y)
    (he : (componentOverlap M K).map e.toMonoidHom = U)
    (hcard : Nat.card B = Nat.card F - 1)
    (t : X) (ht : t ∈ S) (β : MulAut B)
    (hβ : ∀ b : B, (β b : X) = t * (b:X) * t⁻¹) :
    ∃ (χ : B ≃* Fˣ) (σ : F ≃+* F),
      ∀ b : B, χ (β b) = Units.map σ.toMonoidHom (χ b) := by
  have hBK : B ≤ K := by
    have htwo := isPGroup_quotient_of_sup_eq_top K (S : Subgroup X) S.isPGroup' hgen
    intro b hb
    let b' : B := ⟨b,hb⟩
    let q := QuotientGroup.mk' K
    obtain ⟨a,ha⟩ := htwo (q b)
    have ho' : Odd (orderOf (q b)) := ho.of_dvd_nat
      ((orderOf_map_dvd (q.comp B.subtype) b').trans (orderOf_dvd_natCard b'))
    exact (QuotientGroup.eq_one_iff b).mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (ho'.coprime_two_right.pow_right a)
        dvd_rfl (orderOf_dvd_of_pow_eq_one ha)))
  let N := M ⊓ K
  have hBN : B ≤ N := le_inf hBM hBK
  have hHallN : IsHallSubgroup OddHall.oddPrimes (B.subgroupOf N) :=
    OddHall.hall_restrict_of_normalizes hHall hBM inf_le_left (hBN.trans N.le_normalizer)
  let q := QuotientGroup.mk' (sourceKernel M)
  let R := sourceImage M K
  let b := componentBorelEquiv U e he
  let r : N →* U := b.toMonoidHom.comp (q.subgroupMap N)
  have hr : Function.Surjective r := b.surjective.comp (q.subgroupMap_surjective N)
  have htK : t ∈ normalizer (K : Set X) := by simp [normalizer_eq_top]
  have htR : q t ∈ normalizer (R : Set (X ⧸ sourceKernel M)) :=
    K.le_normalizer_map q (mem_map_of_mem q htK)
  let a : MulAut R := R.normalizerMonoidHom ⟨q t,htR⟩
  let α := MulAut.congr e a
  have htN : t ∈ normalizer (N : Set X) :=
    inf_normalizer_le_normalizer_inf (show t ∈ normalizer (M : Set X) ⊓ normalizer (K : Set X)
      from ⟨M.le_normalizer (hSM ht),htK⟩)
  let δ := N.normalizerMonoidHom ⟨t,htN⟩
  have hrα (x : N) : (r (δ x) : Y) = α (r x) := by
    change e ⟨q (t*(x:X)*t⁻¹),_⟩ = e (a (e.symm (e ⟨q x,_⟩)))
    rw [e.symm_apply_apply]
    congr 1
  have hα : ∀ x ∈ U, α x ∈ U := by
    intro x hx
    obtain ⟨y,hy⟩ := hr ⟨x,hx⟩
    have hh := congrArg (fun z : U => (z:Y)) hy
    change (r y : Y) = x at hh
    rw [←hh,←hrα]
    exact (r (δ y)).property
  let j : B.subgroupOf N ≃* B := subgroupOfEquivOfLe hBN
  let γ := MulAut.congr j.symm β
  have hγ (x : B.subgroupOf N) : ((γ x : N) : X) = t*(x:N)*t⁻¹ := hβ (j x)
  have hinter (x : B.subgroupOf N) : (r (γ x) : Y) = α (r x) := by
    have hh : (γ x : N) = δ x := Subtype.ext (hγ x)
    rw [hh,hrα]
  let f := π.comp r
  have hoF : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units,←hcard]
    exact ho
  have hf := OddHall.surjective_restrict_of_odd (B.subgroupOf N) hHallN f
    (hπ.comp hr) hoF
  let χ := MulEquiv.ofBijective (f.comp (B.subgroupOf N).subtype)
    (hf.bijective_of_nat_card_le (by rw [Nat.card_units,←hcard,Nat.card_congr j.toEquiv]))
  obtain ⟨σ,hσ⟩ := hfield α hα
  have hχ (x : B.subgroupOf N) : χ (γ x) = Units.map σ.toMonoidHom (χ x) := by
    have hh : r (γ x) = ⟨α (r x),hα (r x) (r x).property⟩ := Subtype.ext (hinter x)
    change π (r (γ x)) = Units.map σ.toMonoidHom (π (r x))
    rw [hh]
    exact hσ (r x)
  refine ⟨j.symm.trans χ,σ,fun x => ?_⟩
  exact hχ (j.symm x)

/-- Restriction to the original Hall subgroup of a normal, marked linear Borel. -/
theorem normal_linear_borel_hall_action (S : Sylow 2 X) (M K B : Subgroup X)
    [K.Normal] (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hSM : (S : Subgroup X) ≤ M) (hBM : B ≤ M)
    (hHall : IsHallSubgroup OddHall.oddPrimes (B.subgroupOf M))
    (ho : Odd (Nat.card B))
    (e : sourceImage M K ≃* SL(2,F))
    (he : (componentOverlap M K).map e.toMonoidHom = rankOneBorel F)
    (hcard : Nat.card B = Nat.card F - 1)
    (t : X) (ht : t ∈ S) (β : MulAut B)
    (hβ : ∀ b : B, (β b : X) = t * (b:X) * t⁻¹) :
    ∃ (χ : B ≃* Fˣ) (σ : F ≃+* F),
      ∀ b : B, χ (β b) = Units.map σ.toMonoidHom (χ b) := by
  exact normal_borel_hall_field_action S M K B hgen hSM hBM hHall ho
    (rankOneBorel F) borelDiagonalProjection borelDiagonalProjection_surjective
    borel_preserver_field_action e he hcard t ht β hβ

private theorem odd_dvd_hall_card {A : Type*} [Group A] [Finite A]
    (B : Subgroup A) (hB : IsHallSubgroup OddHall.oddPrimes B)
    {d : ℕ} (ho : Odd d) (hd : d ∣ Nat.card A) : d ∣ Nat.card B := by
  have hc : Nat.Coprime d B.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpi
    apply hB.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpi
    intro he
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (he ▸ hpd))
  apply hc.dvd_of_dvd_mul_right
  rwa [B.card_mul_index]

private theorem nearby_mersenne_degree {f n : ℕ} (hn : 3 ≤ n)
    (hf : n-1 ≤ f) (hd : 2^f-1 ∣ 2^n-1) : f = n := by
  have hpow : 2^f ≤ 2^n := by
    have hp : 0 < 2^f := pow_pos (by decide) f
    have hq : 1 < 2^n := Nat.one_lt_two_pow (by omega)
    have hh := Nat.le_of_dvd (by omega : 0 < 2^n-1) hd
    omega
  have hfn : f ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  by_contra hne
  have hn' : n = f+1 := by omega
  have hf2 : 2 ≤ f := by omega
  have h4 : 4 ≤ 2^f := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf2
  rw [hn',pow_succ] at hd
  have hsub : 2^f*2-1 = 2*(2^f-1)+1 := by omega
  rw [hsub] at hd
  have hd1 : 2^f-1 ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_left (2^f-1) 2)).mpr hd
  have he1 := Nat.le_of_dvd (by decide : 0 < 1) hd1
  omega

/-- A source linear component admits a marking of its original Borel over
 the prescribed binary field. No action or generation equality is assumed. -/
theorem source_binary_linear_borel_marking
    {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax S hP) K) 2 (2^f)) :
    ∃ e : sourceImage (ChapterB.minimalParabolicMax S hP) K ≃* SL(2,GaloisField 2 f),
      (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map e.toMonoidHom =
        rankOneBorel (GaloisField 2 f) := by
  let R := sourceImage (ChapterB.minimalParabolicMax S hP) K
  obtain ⟨P,hP'⟩ := source_bender_sylow_normalizer S hP hs K hK hgen (.linear f hf hm)
  obtain ⟨E,hE,hfin,hcard,⟨e₀⟩⟩ := hm
  let : Fintype E := Fintype.ofFinite E
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let eF : E ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,GaloisField.card 2 f (by omega)] using hcard)
  let e₁ : R ≃* SL(2,GaloisField 2 f) :=
    (e₀.trans (GorensteinWalter.psl2RingEquiv eF)).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 f)).symm
  let Q := P.mapSurjective (f := e₁.toMonoidHom) e₁.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,GaloisField 2 f) Q
    (upperUnipotentSylow (GaloisField 2 f) 2)
  let e := e₁.trans (MulAut.conj g)
  have hPe : (P : Subgroup R).map e.toMonoidHom = upperUnipotent (GaloisField 2 f) := by
    change (P : Subgroup R).map ((MulAut.conj g).toMonoidHom.comp e₁.toMonoidHom) = _
    rw [←map_map]
    change ((g • Q : Sylow 2 SL(2,GaloisField 2 f)) : Subgroup SL(2,GaloisField 2 f)) = _
    rw [hg]
    rfl
  refine ⟨e,?_⟩
  rw [hP']
  change (normalizer ((P : Subgroup R) : Set R)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq,hPe]

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)

include c in
/-- Hall arithmetic identifies any actual source model degree whose torus
has order 2^f-1 and whose generation bound is f. No quotient equality of
generation parameters is used. -/
theorem original_hall_source_degree {n f : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card B = 2^n-1) (hlo : n-1 ≤ generationParameter H)
    (hbound : generationParameter H ≤ f)
    (hmodel : ∃ A : Subgroup H, A ≤ D.maximalLocal.subgroupOf H ∧ Nat.card A = 2^f-1) :
    f = n := by
  obtain ⟨A,hAM,hA⟩ := hmodel
  have hd : 2^f-1 ∣ Nat.card B := by
    have ho : Odd (2^f-1) := Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by omega)) odd_one
    have hd : 2^f-1 ∣ Nat.card (D.maximalLocal.subgroupOf H) := by
      rw [←hA,←Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv]
      exact card_subgroup_dvd_card _
    have hh := odd_dvd_hall_card (B.subgroupOf (D.maximalLocal.subgroupOf H)) c.hall ho hd
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv] at hh
  exact nearby_mersenne_degree hn (hlo.trans hbound) (hcard ▸ hd)

/-- The original H-model's binary linear row is incompatible with the
natural tensor exchanger. Both actions are compared on the same original B. -/
theorem original_hall_conclusion_of_normal_linear_source
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype c.hstar.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T.subtype c.hstar.1.1.2 : Subgroup H) = ⊤)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL
      (sourceImage (ChapterB.minimalParabolicMax (T.subtype c.hstar.1.1.2) hP) K) 2 (2^f)) :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  rcases original_hall_conclusion_or_natural_tensor_inverse_field D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,_ha,_hdet,_heq,_hseed,_hBR,_hcyc,hcard,_hexp,hlo,_hhi,
      C,hC,hBC,_hHall,htC,htB,k,χ,β,σ,_hne,_hpow,hno,hβ,_rest⟩
  · exact hh
  · exfalso
    let S := T.subtype c.hstar.1.1.2
    let M := ChapterB.minimalParabolicMax S hP
    have hM : M = D.maximalLocal.subgroupOf H := source_hstar_parabolicMax_eq_overlap D c.hstar hP
    have hs : ¬Group.IsSolvable H := by
      intro hs
      let := hs
      exact (Nat.not_le_of_gt c.large) generationParameter_le_one_of_solvable
    have hbound := normal_linear_two_parameter_le ChapterA.Section02.theoremA_knownSimple
      (Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1) S hP hs K hK hgen hf hm
    obtain ⟨A,hAM,_hAc,hAc⟩ := (source_linear_borel_model S hP hs K hK hgen hf hm).cyclic
    have hHallB : IsHallSubgroup OddHall.oddPrimes (B.subgroupOf M) := hM.symm ▸ c.hall
    have hBM : B ≤ M := hM.symm ▸ c.hall_le
    have hfn : f = n := original_hall_source_degree D c hn hcard hlo hbound
      ⟨A,hM ▸ hAM,hAc⟩
    subst f
    obtain ⟨eH,heH⟩ := source_binary_linear_borel_marking S hP hs K hK hgen hf hm
    have hβH (b : B) : (β b : H) =
        (⟨t,c.hstar.1.1.2 ht⟩ : H) * (b:H) * (⟨t,c.hstar.1.1.2 ht⟩ : H)⁻¹ :=
      Subtype.ext (hβ b)
    obtain ⟨ψ,τ,hψ⟩ := normal_linear_borel_hall_action S M K B hgen
      (ChapterB.minimalParabolicMax_spec S hP).2 hBM hHallB (HallGeometry.hall_odd D c)
      eH heH (by rw [GaloisField.card 2 n (by omega)];exact hcard)
      ⟨t,c.hstar.1.1.2 ht⟩ ht β hβH
    exact hno ψ τ hψ

/-- An actual Suzuki source component has its original overlap marked as
the standard Borel by the same isomorphism. -/
theorem source_suzuki_borel_marking
    {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Nonempty (sourceImage (ChapterB.minimalParabolicMax S hP) K ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ∃ e : sourceImage (ChapterB.minimalParabolicMax S hP) K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m,
      (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map e.toMonoidHom =
        BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m := by
  let R := sourceImage (ChapterB.minimalParabolicMax S hP) K
  obtain ⟨P,hP'⟩ := source_bender_sylow_normalizer S hP hs K hK hgen (.suzuki m hm hmodel)
  obtain ⟨e⟩ := hmodel
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := ChapterF.Source.suzuki_sylow_normalizer_eq_conjugate_borel m Q
  let d := e.trans (MulAut.conj g⁻¹)
  have hPe : (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map e.toMonoidHom =
      (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m).map (MulAut.conj g).toMonoidHom := by
    rw [hP']
    change (normalizer ((P : Subgroup R) : Set R)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hg
  refine ⟨d,?_⟩
  change (componentOverlap (ChapterB.minimalParabolicMax S hP) K).map
    ((MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom) = _
  rw [←map_map,hPe,map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
    ext x
    simp [mul_assoc]
  rw [he,map_id]

/-- The original normal Suzuki H-model has ordinary field action on the
same B and is therefore incompatible with the tensor exchanger too. -/
theorem original_hall_conclusion_of_normal_suzuki_source
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype c.hstar.1.1.2) ⊤)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T.subtype c.hstar.1.1.2 : Subgroup H) = ⊤)
    {m : ℕ} (hm : 1 ≤ m)
    (hmodel : Nonempty (sourceImage
      (ChapterB.minimalParabolicMax (T.subtype c.hstar.1.1.2) hP) K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1 := by
  rcases original_hall_conclusion_or_natural_tensor_inverse_field D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,_ha,_hdet,_heq,_hseed,_hBR,_hcyc,hcard,_hexp,hlo,_hhi,
      C,hC,hBC,_hHall,htC,htB,k,χ,β,σ,_hne,_hpow,hno,hβ,_rest⟩
  · exact hh
  · exfalso
    let S := T.subtype c.hstar.1.1.2
    let M := ChapterB.minimalParabolicMax S hP
    have hM : M = D.maximalLocal.subgroupOf H := source_hstar_parabolicMax_eq_overlap D c.hstar hP
    have hs : ¬Group.IsSolvable H := by
      intro hs
      let := hs
      exact (Nat.not_le_of_gt c.large) generationParameter_le_one_of_solvable
    have hbound := (normal_suzuki_generation S hP hs K hK hgen (by omega) hmodel).2
    obtain ⟨A,hAM,_hAc,hAc⟩ := (source_suzuki_borel_model S hP hs K hK hgen hm hmodel).cyclic
    have hfn : 2*m+1 = n := original_hall_source_degree D c hn hcard hlo hbound
      ⟨A,hM ▸ hAM,hAc⟩
    subst n
    obtain ⟨eH,heH⟩ := source_suzuki_borel_marking S hP hs K hK hgen hm hmodel
    have hβH (b : B) : (β b : H) =
        (⟨t,c.hstar.1.1.2 ht⟩ : H) * (b:H) * (⟨t,c.hstar.1.1.2 ht⟩ : H)⁻¹ :=
      Subtype.ext (hβ b)
    obtain ⟨ψ,τ,hψ⟩ := normal_borel_hall_field_action S M K B hgen
      (ChapterB.minimalParabolicMax_spec S hP).2 (hM.symm ▸ c.hall_le)
      (hM.symm ▸ c.hall) (HallGeometry.hall_odd D c)
      (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m)
      (BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient.projection m (by omega))
      (BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient.projection_surjective m (by omega))
      (BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient.borel_preserver_field_action m (by omega))
      eH heH (by rw [GaloisField.card 2 (2*m+1) (by omega)];exact hcard)
      ⟨t,c.hstar.1.1.2 ht⟩ ht β hβH
    exact hno ψ τ hψ

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
