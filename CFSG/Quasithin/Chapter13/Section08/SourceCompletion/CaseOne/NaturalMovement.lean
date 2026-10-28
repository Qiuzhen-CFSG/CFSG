module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalIntersections
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Action
public import Theory.GroupTheory.PResidual.OddImage
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Full movement of the nonorthogonal seed intersection

For the actual nonorthogonal pair, the two-point span is a nondegenerate
plane in the original natural module. Its complementary cubic axis lifts
through the original LT action into O²(C_{L₁}(V₁ V₁ˡ)): two-residuals preserve
its odd image, and a second residual keeps the same lifted subgroup.
This uses the literal parabolic residual, without asserting ambient normality.

The source complement W₂ is normalized by that residual. Since the
residual fixes V₁ V₁ˡ, its displacements on V lie in [W₂,X₁]. The cubic
model supplies two independent displacements, proving [W₂,X₁] = W₂.
The final theorem applies this to the constructed nonabelian source
conjugator and retains both complements, its square and its star image.

The ordinary setup and full denominators are the earlier input and contrary
branch of 13.8.33. The star/core intersection, chief-factor contradiction,
Steinberg/permutation comparisons and 13.4.1 application remain with
`qt-d-138-a6-endgame-source`; ordinary setup is supplied by
`qt-d-138-six-g2-source`. No strict denominator or chief count is assumed.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, final paragraph.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

private theorem cubic_residual_eq (B : Subgroup (Equiv.Perm (Fin 6))) (hc : Nat.card B = 3) :
    (pResidual 2 B).map B.subtype = B := by
  have hr : pResidual 2 B = ⊤ := by
    apply top_unique
    intro b _
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (hc ▸ _root_.orderOf_dvd_natCard b)
  rw [hr, ← MonoidHom.range_eq_map, range_subtype]

private theorem pair_residual_lifts_cubic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (P : Subgroup G)
    (hPV : P ≤ V) (hline : V₁ ≤ P)
    (B : Subgroup (Equiv.Perm (Fin 6))) (hc : Nat.card B = 3)
    (hB : B ≤ alternatingGroup (Fin 6))
    (hfix : ∀ b ∈ B, ∀ v : V, (v : G) ∈ P →
      naturalRepresentation (Fin 6) b (d.coordinate v).toAdd = (d.coordinate v).toAdd) :
    ∀ b ∈ B, ∃ x : (L ⊔ (T : Subgroup G) : Subgroup G),
      (x : G) ∈ residual (sourceOne L T V₁ ⊓ centralizer (P : Set G)) ∧
      Section07.NaturalAction.permutation (localNaturalSetup d) x = b := by
  let K := L ⊔ (T : Subgroup G)
  let f := Section07.NaturalAction.permutation (localNaturalSetup d)
  let D := B.comap f
  let R := (pResidual 2 D).map D.subtype
  have hDf : D.map f = B := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (hB.trans (Section07.NaturalAction.alternating_le_range (localNaturalSetup d)))
  have hRf : R.map f = B := by
    rw [show R = (pResidual 2 D).map D.subtype from rfl,
      map_embedded_pResidual, hDf, cubic_residual_eq B hc]
  have hDP : D.map K.subtype ≤ centralizer (P : Set G) := by
    rintro _ ⟨x, hx, rfl⟩ v hv
    have he := Section07.NaturalAction.conjugation (localNaturalSetup d) x ⟨v, hPV hv⟩
    change (d.coordinate (V.normalizerMonoidHom _ ⟨v, hPV hv⟩)).toAdd =
      naturalRepresentation (Fin 6) (f x) (d.coordinate ⟨v, hPV hv⟩).toAdd at he
    rw [hfix (f x) hx ⟨v, hPV hv⟩ hv] at he
    have he' := congrArg Subtype.val (d.coordinate.injective he)
    change (x : G) * v * (x : G)⁻¹ = v at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hDpar : D.map K.subtype ≤ parabolic L (T : Subgroup G) V₁ :=
    le_inf (map_subtype_le _) ((hDP.trans (centralizer_le hline)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hRone : R.map K.subtype ≤ sourceOne L T V₁ := by
    rw [show R = (pResidual 2 D).map D.subtype from rfl, map_embedded_pResidual]
    exact embedded_pResidual_mono 2 hDpar
  have hRCP : R.map K.subtype ≤ sourceOne L T V₁ ⊓ centralizer (P : Set G) :=
    le_inf hRone ((map_mono (map_subtype_le (pResidual 2 D))).trans hDP)
  have hRres : R.map K.subtype ≤ residual (sourceOne L T V₁ ⊓ centralizer (P : Set G)) := by
    have hm := embedded_pResidual_mono 2 hRCP
    rw [(pResidual_eq_top_iff 2 _).mpr
      ((isPPerfect_embedded_pResidual 2 D).of_surjective
        (K.subtype.subgroupMap R) (K.subtype.subgroupMap_surjective R)),
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm
  intro b hb
  obtain ⟨x, hx, hxb⟩ := hRf.ge hb
  exact ⟨x, hRres (mem_map_of_mem _ hx), hxb⟩

private theorem pair_residual_moves_complement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (P W : Subgroup G)
    (hPV : P ≤ V) (hline : V₁ ≤ P) (hPc : Nat.card P = 4)
    (hn : ¬ ∀ x ∈ Section07.NaturalAction.image (localNaturalSetup d) P,
      ∀ y ∈ Section07.NaturalAction.image (localNaturalSetup d) P, form x y = 0)
    (hWV : W ≤ V) (hWc : Nat.card W = 4) (hjoin : P ⊔ W = V)
    (hXW : residual (sourceOne L T V₁ ⊓ centralizer (P : Set G)) ≤
      normalizer (W : Set G)) :
    ⁅W, residual (sourceOne L T V₁ ⊓ centralizer (P : Set G))⁆ = W := by
  let n := localNaturalSetup d
  let X := residual (sourceOne L T V₁ ⊓ centralizer (P : Set G))
  let E := Section07.NaturalAction.image n P
  have hdim : Module.finrank (ZMod 2) E = 2 :=
    Section07.NaturalAction.image_dim n P hPV 2 hPc
  obtain ⟨A, B, _, hBc, _, _, _, hEven, _, _, _, _, _, hmov, _, hfix⟩ :=
    exists_cubic_decomposition E hdim hn
  have hBX := pair_residual_lifts_cubic d P hPV hline B hBc
    (le_sup_right.trans hEven) (fun b hb v hv => hfix b hb _ ⟨v, hv, rfl⟩)
  have hXL : X ≤ L ⊔ (T : Subgroup G) :=
    (residual_le _).trans (inf_le_left.trans ((one_le _ _ _).trans inf_le_left))
  have hXP : X ≤ centralizer (P : Set G) := (residual_le _).trans inf_le_right
  have hCW : ⁅W, X⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hXW
  have hCV := hCW.trans hWV
  let : IsMulCommutative V := (Section07.NaturalAction.elementary n).toIsMulCommutative
  have hVC : V ≤ normalizer ((⁅W, X⁆ : Subgroup G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro v hv c hc
    exact congrArg Subtype.val (mul_comm (⟨c, hCV hc⟩ : V) ⟨v, hv⟩)
  have hVX : ⁅V, X⁆ ≤ ⁅W, X⁆ := by
    rw [← hjoin]
    apply commutator_sup_le_of_relative_normal V P W X ⁅W, X⁆ hVC hPV hWV
    · rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hXP)]
      exact bot_le
    · exact le_rfl
  have hm : movedSpace B ≤ Section07.NaturalAction.image n ⁅W, X⁆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, v⟩, rfl⟩
    obtain ⟨x, hx, hxb⟩ := hBX b b.property
    obtain ⟨u, hu⟩ := d.coordinate.surjective (Multiplicative.ofAdd v)
    let c := V.normalizerMonoidHom ⟨x.val, d.normalizes_V x.property⟩ u * u⁻¹
    refine ⟨c, ?_, ?_⟩
    · apply hVX
      rw [commutator_comm]
      exact commutator_mem_commutator hx u.property
    · change (d.coordinate (V.normalizerMonoidHom _ u * u⁻¹)).toAdd =
        naturalRepresentation (Fin 6) (b : Equiv.Perm (Fin 6)) v - v
      have he := Section07.NaturalAction.conjugation n x u
      change (d.coordinate (V.normalizerMonoidHom _ u)).toAdd =
        naturalRepresentation (Fin 6) (Section07.NaturalAction.permutation n x)
          (d.coordinate u).toAdd at he
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg, he, hxb, hu]
      rfl
  have hperp : Module.finrank (ZMod 2) (movedSpace B) = 2 := by
    rw [hmov, LinearMap.BilinForm.finrank_orthogonal form_nondegenerate, hdim,
      finrank_natural_even (Fin 6) (by decide)]
    decide
  have hi : Section07.NaturalAction.image n ⁅W, X⁆ ≤ Section07.NaturalAction.image n W := by
    rintro v ⟨u, hu, rfl⟩
    exact ⟨u, hCW hu, rfl⟩
  have hdW : Module.finrank (ZMod 2) (Section07.NaturalAction.image n W) = 2 :=
    Section07.NaturalAction.image_dim n W hWV 2 hWc
  have he : Section07.NaturalAction.image n ⁅W, X⁆ = Section07.NaturalAction.image n W := by
    apply Submodule.eq_of_le_of_finrank_eq hi
    apply le_antisymm (Submodule.finrank_mono hi)
    exact hdW.le.trans (hperp.ge.trans (Submodule.finrank_mono hm))
  apply le_antisymm hCW
  intro w hw
  have hwc : (d.coordinate ⟨w, hWV hw⟩).toAdd ∈ Section07.NaturalAction.image n ⁅W, X⁆ :=
    he.symm ▸ (show (d.coordinate ⟨w, hWV hw⟩).toAdd ∈ Section07.NaturalAction.image n W from
      ⟨⟨w, hWV hw⟩, hw, rfl⟩)
  obtain ⟨v, hv, hvw⟩ := hwc
  have hval : (v : G) = w := congrArg Subtype.val (d.coordinate.injective hvw)
  exact hval ▸ hv

/-- The literal point-pair two-residual moves the whole seed intersection.
The order and complement premises are supplied by the preceding source
intersection theorem, with the original nonorthogonal conjugator. -/
theorem nonorthogonal_seed_intersection_moved
    {H : Subgroup G} (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁)
    (l : L) (hout : ¬ V₁.conjBy (l : G) ≤ V₃)
    (hcard : Nat.card (V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G) : Subgroup G) = 4)
    (hjoin : (V₁ ⊔ V₁.conjBy (l : G)) ⊔
      (V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)) = V)
    (hdis : Disjoint (V₁ ⊔ V₁.conjBy (l : G))
      (V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G))) :
    let W := V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)
    let X := residual (sourceOne L T V₁ ⊓
      centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
    ⁅W, X⁆ = W := by
  dsimp only
  let P := V₁ ⊔ V₁.conjBy (l : G)
  let W := V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)
  let n := localNaturalSetup d
  have hlineV : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hPV : P ≤ V := by
    apply sup_le hlineV
    have he : V.conjBy (l : G) = V :=
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes_V (mem_sup_left l.property))
    exact (map_mono hlineV).trans he.le
  have hWV : W ≤ V := inf_le_left.trans inf_le_left
  let : IsMulCommutative V := (Section07.NaturalAction.elementary n).toIsMulCommutative
  have hnorm : W ≤ normalizer (P : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro w hw p hp
    exact congrArg Subtype.val (mul_comm (⟨p, hPV hp⟩ : V) ⟨w, hWV hw⟩)
  have hcV : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    decide
  have hmul := card_sup_eq_mul_of_normalizes_of_disjoint P W hnorm hdis
  rw [hjoin, hcard, hcV] at hmul
  have hPc : Nat.card P = 4 := by omega
  apply pair_residual_moves_complement d P W hPV le_sup_left hPc ?_ hWV hcard hjoin
    (pair_residual_normalizes d hH l).2.2
  intro hiso
  apply hout
  intro v hv
  have hvin : (d.coordinate ⟨v, hPV (mem_sup_right hv)⟩).toAdd ∈
      Section07.NaturalAction.image n V₃ := by
    rw [Section07.NaturalAction.seed_perpendicular]
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact hiso _ ⟨u, mem_sup_left hu, rfl⟩ _
      ⟨⟨v, hPV (mem_sup_right hv)⟩, mem_sup_right hv, rfl⟩
  obtain ⟨u, hu, huv⟩ := hvin
  have he : (u : G) = v := congrArg Subtype.val (d.coordinate.injective huv)
  exact he ▸ hu

/-- In the contrary nonabelian branch, choose the source conjugator and
construct both complements and their full point-pair residual movement.
All the earlier endpoint and ordinary-setup inputs are unchanged. -/
theorem exists_nonabelian_seed_movement
    {H : Subgroup G} [IsElementaryAbelian 2 (Source.UH H V₃)]
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      V ≤ V₃ ⊔ V₁.conjBy (l : G) ∧
      ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) ≠ ⊥ ∧
      let W := V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)
      Disjoint V₁ W ∧ V₁ ⊔ W = V₃ ∧ Nat.card W = 4 ∧
        W = V₃ ⊓ V₃.conjBy (l : G) ∧
        Disjoint (V₁ ⊔ V₁.conjBy (l : G)) W ∧
        (V₁ ⊔ V₁.conjBy (l : G)) ⊔ W = V ∧
        let X := residual (sourceOne L T V₁ ⊓
          centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
        X ≤ normalizer (Source.UH H V₃ : Set G) ∧
          X ≤ normalizer ((Source.UH H V₃).conjBy (l : G) : Set G) ∧
          X ≤ normalizer (W : Set G) ∧ ⁅W, X⁆ = W := by
  obtain ⟨l, hs, hspan, hout, hlH, hstar, hW⟩ :=
    exists_nonabelian_seed_intersection d hF9 c hH hDH hDg hcentral hn
  dsimp only at hW ⊢
  refine ⟨l, hs, hspan, hout, hlH, hstar, hW.1, hW.2.1, hW.2.2.1,
    hW.2.2.2.1, hW.2.2.2.2.1, hW.2.2.2.2.2.1,
    hW.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.2, ?_⟩
  exact nonorthogonal_seed_intersection_moved d hH l hout hW.2.2.1
    hW.2.2.2.2.2.1 hW.2.2.2.2.1

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
