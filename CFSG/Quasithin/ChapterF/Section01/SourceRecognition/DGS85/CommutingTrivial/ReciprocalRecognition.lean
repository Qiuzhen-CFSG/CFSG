module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReverseDisplacement
public import Theory.Representation.RankOne.QuadraticRecognition.ElementFixedSpaces

/-!
# Reciprocal residual indices and natural modules in the large-neighbor case

Apply corrected 5.12 to the two literal residual sections. Each original
core index bounds the other, so they are equal. Both are greater than one,
which supplies the strict-square comparison and natural recognition in both
directions. The faithful linear-action bound identifies these indices with
the field orders and with the source omega-center parameters in every actual
local-quotient Sylow.

Reverse zero displacement is proved using the existing Chapter 9 exchange
and its explicit Chapter 8 premise (producer
qt-dgs85-critical-commuting-nontrivial). The exact earlier 6.5 obstructions
retain qt-dgs85-setup-obstruction as producer. Actual linear quotient
markings and action descent remain explicit; this conditional step does not
recognize those quotients or prove the Chapter 9 distance bound. Initial
recognition, the small-neighbor case and final assembly remain with this
Chapter 9 owner.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
9.2--9.3, printed p.142, and corrected 5.12, printed pp.113--115.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

private theorem reciprocal_residual_indices
    {F K W U : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (τ : Representation (ZMod 2) SL(2,K) U)
    (A : Subgroup SL(2,F)) (B : Subgroup SL(2,K))
    {n m x y : ℕ} (hF : Nat.card F = 2^n) (hK : Nat.card K = 2^m)
    (hx : 1 < x) (hy : 1 < y)
    (hσ : ResidualIndexControl σ A n y x)
    (hτ : ResidualIndexControl τ B m x y) :
    x = y ∧ x = Nat.card F ∧ y = Nat.card K ∧
      ∃ (S : Sylow 2 SL(2,F)) (T : Sylow 2 SL(2,K)),
        IsSourceNatural σ S n ∧ IsSourceNatural τ T m := by
  obtain ⟨S,hAS,_,hfσ,hAc,hloσ,huσ,hnatσ⟩ := hσ
  obtain ⟨T,hBT,_,hfτ,hBc,hloτ,huτ,hnatτ⟩ := hτ
  have he : x = y := le_antisymm (hBc ▸ hloτ.trans huτ) (hAc ▸ hloσ.trans huσ)
  have hA : A ≠ ⊥ := by intro he; rw [he,card_bot] at hAc; omega
  have hB : B ≠ ⊥ := by intro he; rw [he,card_bot] at hBc; omega
  have hflo := (sl2_actor_field_bound σ hfσ S A hAS hA hF).trans huσ
  have hklo := (sl2_actor_field_bound τ hfτ T B hBT hB hK).trans huτ
  have hfhi : x ≤ Nat.card F := by
    rw [he,←hAc]
    exact (Nat.card_le_card_of_injective _ (inclusion_injective hAS)).trans_eq
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv)
  have hkhi : y ≤ Nat.card K := by
    rw [←he,←hBc]
    exact (Nat.card_le_card_of_injective _ (inclusion_injective hBT)).trans_eq
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 T).symm.toEquiv)
  exact ⟨he,le_antisymm hfhi hflo,le_antisymm hkhi hklo,S,T,
    (hnatσ (by nlinarith)).1,(hnatτ (by nlinarith)).1⟩

private theorem linear_sylow_parameter {D F : Type*} [Group D] [Finite D]
    [Field F] [Finite F] [CharP F 2] (e : D ≃* SL(2,F)) (R : Sylow 2 D) :
    Nat.card (omegaCenterIn (R : Subgroup D)) = Nat.card F := by
  let T := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : (omegaCenterIn (R : Subgroup D)).map e.toMonoidHom = T := by
    rw [NilesRankOneKernel.omegaCenterIn_map_injective _ e.injective]
    change omegaCenterIn (T : Subgroup SL(2,F)) = T
    rw [omegaCenterIn_eq_omegaOneAmbient,sl2_omega_center_eq]
  calc
    Nat.card (omegaCenterIn (R : Subgroup D)) =
        Nat.card ((omegaCenterIn (R : Subgroup D)).map e.toMonoidHom) :=
      (card_map_of_injective e.injective).symm
    _ = Nat.card T := congrArg (fun C : Subgroup SL(2,F) => Nat.card C) hm
    _ = Nat.card F := Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv

universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- In the large-neighbor case, the two original quotient actions force
both core indices to equal the two field orders and make both literal
residual sections natural. The strict comparison is proved, not supplied. -/
theorem reduced_large_neighbor_residual_natural (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F)))
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (hob' : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj a' z →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ¬ stabilizer (Reduction.reducedFamily L S₀) z ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) a' ⊓ Q (Reduction.reducedFamily L S₀) z :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    {n m : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) (hm : 0 < m) (hK : Nat.card K = 2^m)
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (e' : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let H' := graphLocalGroup Γ a'
    let A := (V Γ beta 1).subgroupOf H
    let A' := (V Γ a' 1).subgroupOf H'
    let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    let q' := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H'))
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    letI := neighborhoodIn_normal Γ a' H' (sylowGenerated_le _)
    ∀ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 H'
      ∀ (σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)))
        (τ : Representation (ZMod 2) SL(2,K) (FixedQuotient A' (pResidual 2 H'))),
        (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) →
        (∀ l : H', τ (q' l) = fixedQuotientAction A' (pResidual 2 H') l) →
        (Q Γ a').relIndex (V Γ beta 1) = (Q Γ beta).relIndex (V Γ a' 1) ∧
          (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
          (Q Γ beta).relIndex (V Γ a' 1) = Nat.card K ∧
          (∀ (T₀ : Sylow 2 (H ⧸ pCore 2 H)) (R₀ : Sylow 2 (H' ⧸ pCore 2 H')),
            (Q Γ a').relIndex (V Γ beta 1) = Nat.card (omegaCenterIn (T₀ : Subgroup (H ⧸ pCore 2 H))) ∧
            (Q Γ beta).relIndex (V Γ a' 1) = Nat.card (omegaCenterIn (R₀ : Subgroup (H' ⧸ pCore 2 H')))) ∧
          ∃ (T : Sylow 2 SL(2,F)) (R : Sylow 2 SL(2,K)),
            IsSourceNatural σ T n ∧ IsSourceNatural τ R m := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let H' := graphLocalGroup Γ a'
  let A := (V Γ beta 1).subgroupOf H
  let A' := (V Γ a' 1).subgroupOf H'
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  let := neighborhoodIn_normal Γ a' H' (sylowGenerated_le _)
  dsimp only
  intro hb2
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 H'
  intro σ τ hσ hτ
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  have hforward : ResidualIndexControl σ
      (((V Γ a' 1).subgroupOf H).map (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))))
      n ((Q Γ beta).relIndex (V Γ a' 1))
      ((centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1)) :=
    reduced_critical_residual_index_recognition h hc hab hd hb hcomm hob hn hF eβ hb2 σ hσ
  have hback : ResidualIndexControl τ
      (((V Γ beta 1).subgroupOf H').map (e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H'))))
      m ((Q Γ a').relIndex (V Γ beta 1))
      ((centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1)) :=
    reduced_critical_residual_index_recognition h hzc hz.symm hd' hb hzcomm
    (hob' z hz hzc) hm hK e' hb2 τ hτ
  have hfwd : V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) =
      V Γ beta 1 ⊓ Q Γ a' := reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv
  have hbwd : V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) =
      V Γ a' 1 ⊓ Q Γ beta := reduced_neighbor_centralizer_eq_core_inter h a' beta hb hd' hrev
  have hc₁ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    hfwd
  have hc₂ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    hbwd
  simp only [inf_relIndex_left] at hc₁ hc₂
  rw [hc₁] at hforward
  rw [hc₂] at hback
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite H' := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (FixedQuotient A (pResidual 2 H)) :=
    Finite.of_surjective _ (fixedSpace (originalAction A) (pResidual 2 H)).mkQ_surjective
  let : Finite (FixedQuotient A' (pResidual 2 H')) :=
    Finite.of_surjective _ (fixedSpace (originalAction A') (pResidual 2 H')).mkQ_surjective
  have heforward : ¬ V Γ beta 1 ≤ Q Γ a' :=
    V_not_le_Q_of_criticalPair Γ hc hab.symm (source_Z_Q_U ht a').2
  have hv : V Γ beta 1 ≤ H := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) beta beta hb
    (show (graph Γ).dist beta beta + 1 ≤ b Γ by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  have hw : V Γ a' 1 ≤ H' := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) a' a' hb
    (show (graph Γ).dist a' a' + 1 ≤ b Γ by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hv) (inclusion_injective _)
  let : Finite (V Γ a' 1) := Finite.of_injective (inclusion hw) (inclusion_injective _)
  have hx : 1 < (Q Γ a').relIndex (V Γ beta 1) :=
    one_lt_index_of_ne_top (fun heq => heforward (subgroupOf_eq_top.mp heq))
  have hy : 1 < (Q Γ beta).relIndex (V Γ a' 1) :=
    one_lt_index_of_ne_top (fun heq => he (subgroupOf_eq_top.mp heq))
  obtain ⟨hxy,hfield,hfield',hnat⟩ :=
    reciprocal_residual_indices σ τ _ _ hF hK hx hy hforward hback
  exact ⟨hxy,hfield,hfield',fun T R =>
    ⟨hfield.trans (linear_sylow_parameter eβ T).symm,
      hfield'.trans (linear_sylow_parameter e' R).symm⟩,hnat⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
