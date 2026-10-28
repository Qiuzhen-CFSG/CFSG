module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Reductions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.PowerCover
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.FiniteParabolicTransfer
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M12.Reduction

/-!
# Invariant local seeds in the original E.6.8 component

A subgroup in the specified quotient L/O₂(L) is pulled back with its full
central two-kernel. Stabilizer invariance of the model seed gives invariance
under N_Q(L), allowing Q to permute the components of C_G(U). The component
orbit construction then supplies characteristic two and a normal cover by
powers of the full native seed. An abelian-square obstruction excludes the
actual subnormal chi-zero blocks, so the genuine E.6.7 decomposition places
the lift in M. These transfers do not assume C_G(z) ≤ M.

Source: Aschbacher–Smith, E.6.7–8, printed pp.246–248 (PDF pp.257–259).
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
variable {G A : Type*} [Group G] [Finite G] [Group A]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The actual two-core quotient followed by the supplied model marking. -/
def modelMap (e : (L ⧸ pCore 2 L) ≃* A) : L →* A :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

omit [Finite G] in
theorem modelMap_surjective (e : (L ⧸ pCore 2 L) ≃* A) :
    Function.Surjective (modelMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem modelMap_ker (e : (L ⧸ pCore 2 L) ≃* A) :
    (modelMap e).ker = pCore 2 L := by
  rw [modelMap, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- Transport of the genuine quotient action. -/
def modelAction (e : (L ⧸ pCore 2 L) ≃* A) : MulAut L →* MulAut A :=
  (MulAut.congr e).toMonoidHom.comp (quotientAut (pCore 2 L))

omit [Finite G] in
theorem modelAction_apply (e : (L ⧸ pCore 2 L) ≃* A) (a : MulAut L) (x : L) :
    modelAction e a (modelMap e x) = modelMap e (a x) := by
  change e (quotientAut (pCore 2 L) a (e.symm (e (QuotientGroup.mk' _ x)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

omit [Finite G] in
private theorem component_quasisimple
    (hL : ComponentIn (centralizer (U : Set G)) L) : IsQuasisimple L := by
  let _ := hL.2.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)

/-- Perfectness makes the action faithful despite the retained central kernel. -/
theorem modelAction_injective (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* A) : Function.Injective (modelAction e) := by
  let _ := component_quasisimple hL
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  apply MulAut.eq_one_of_central_displacement
  intro x
  apply IsQuasisimple.pCore_le_center 2
  rw [← modelMap_ker e]
  change modelMap e (x⁻¹ * a x) = 1
  rw [map_mul, map_inv, ← modelAction_apply, show modelAction e a = 1 from ha,
    MulAut.one_apply, inv_mul_cancel]

/-- Full inverse image, embedded in the original ambient group. -/
def seedLift (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) : Subgroup G :=
  (P.comap (modelMap e)).map L.subtype

omit [Finite G] in
theorem seedLift_le (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) :
    seedLift e P ≤ L := map_subtype_le _

omit [Finite G] in
theorem mem_seedLift (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) (x : L) :
    (x : G) ∈ seedLift e P ↔ modelMap e x ∈ P :=
  mem_map_iff_mem L.subtype_injective

/-- The full lifted seed surjects onto its specified native subgroup. -/
def seedProjection (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) : seedLift e P →* P :=
  ((modelMap e).comp (inclusion (seedLift_le e P))).codRestrict P (fun x =>
    (mem_seedLift e P _).mp x.property)

omit [Finite G] in
theorem seedProjection_surjective (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) :
    Function.Surjective (seedProjection e P) := by
  intro y
  obtain ⟨x, hx⟩ := modelMap_surjective e y
  refine ⟨⟨x, (mem_seedLift e P x).mpr (hx.symm ▸ y.property)⟩, ?_⟩
  exact Subtype.ext hx

omit [Finite G] in
theorem seedProjection_ker_two (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) :
    IsPGroup 2 (seedProjection e P).ker := by
  have he : (seedProjection e P).ker =
      (pCore 2 L).comap (inclusion (seedLift_le e P)) := by
    ext x
    change (⟨modelMap e (inclusion (seedLift_le e P) x), _⟩ : P) = 1 ↔ _
    rw [Subtype.ext_iff, ← modelMap_ker e]
    rfl
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

theorem seedProjection_ker_central (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A) :
    (seedProjection e P).ker ≤ center (seedLift e P) := by
  let _ := component_quasisimple hL
  intro x hx
  have hk : inclusion (seedLift_le e P) x ∈ pCore 2 L := by
    rw [← modelMap_ker e]
    exact congrArg Subtype.val hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (congrArg (fun l : L => (l : G))
    (mem_center_iff.mp (IsQuasisimple.pCore_le_center 2 hk) (inclusion (seedLift_le e P) y)))

omit [Finite G] in
theorem seedProjection_kills_center (e : (L ⧸ pCore 2 L) ≃* A)
    (hZ : center A = ⊥) (P : Subgroup A) (x : seedLift e P)
    (hx : inclusion (seedLift_le e P) x ∈ center L) : seedProjection e P x = 1 := by
  apply Subtype.ext
  have hc : modelMap e (inclusion (seedLift_le e P) x) ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l, rfl⟩ := modelMap_surjective e y
    simpa only [map_mul] using congrArg (modelMap e) (mem_center_iff.mp hx l)
  exact mem_bot.mp (hZ ▸ hc)

/-- Characteristic two lifts through the full two-kernel. -/
theorem seedLift_characteristicTwo (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A)
    (hp : HasCharacteristicTwo P) : HasCharacteristicTwo (seedLift e P) := by
  let _ : Finite A := Finite.of_surjective _ (modelMap_surjective e)
  let f := seedProjection e P
  have hcore := f.comap_pCore_of_ker_isPGroup (seedProjection_surjective e P)
    (seedProjection_ker_two e P)
  intro x hx
  rw [← hcore]
  apply hp
  intro y hy
  obtain ⟨z, rfl⟩ := seedProjection_surjective e P y
  have hz : z ∈ pCore 2 (seedLift e P) := by rwa [← hcore]
  simpa only [map_mul] using congrArg f (hx z hz)

/-- The component stabilizer preserves the marked Sylow and hence the lifted seed. -/
theorem seedLift_stable (e : (L ⧸ pCore 2 L) ≃* A) (S : Sylow 2 L)
    {Q : Subgroup G} (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (P : Subgroup A)
    (hinv : ∀ a : MulAut A, ((S : Subgroup L).map (modelMap e)).map a.toMonoidHom =
      (S : Subgroup L).map (modelMap e) → P.map a.toMonoidHom = P) :
    Q ⊓ normalizer (L : Set G) ≤ normalizer (seedLift e P : Set G) := by
  let _ : Finite A := Finite.of_surjective _ (modelMap_surjective e)
  have memS (x : L) : x ∈ (S : Subgroup L) ↔ (x : G) ∈ Q := by
    rw [← mem_map_iff_mem L.subtype_injective, hS]
    exact and_iff_right x.property
  intro g hg
  let a := L.normalizerMonoidHom ⟨g, hg.2⟩
  have hs (x : L) (hx : x ∈ (S : Subgroup L)) : a x ∈ (S : Subgroup L) := by
    apply (memS _).mpr
    exact Q.mul_mem (Q.mul_mem hg.1 ((memS x).mp hx)) (Q.inv_mem hg.1)
  have ha : ((S : Subgroup L).map (modelMap e)).map (modelAction e a).toMonoidHom =
      (S : Subgroup L).map (modelMap e) := by
    apply eq_of_le_of_card_ge
    · rintro y ⟨_, ⟨x,hx,rfl⟩,rfl⟩
      change modelAction e a (modelMap e x) ∈ _
      rw [modelAction_apply]
      exact mem_map_of_mem _ (hs x hx)
    · exact (Nat.card_congr ((modelAction e a).subgroupMap _).toEquiv).le
  have hP := hinv (modelAction e a) ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro y ⟨_, ⟨x,hx,rfl⟩,rfl⟩
    apply (mem_seedLift e P (a x)).mpr
    rw [← modelAction_apply]
    exact hP ▸ mem_map_of_mem _ hx
  · exact (Nat.card_congr ((MulAut.conj g).subgroupMap _).toEquiv).le

/-- A square-controlled native seed is placed in M by the full E.6.7 source.
The component orbit and the two-core kernels are constructed internally. -/
theorem seedLift_le_M_of_squareControl [Finite A]
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* A) (hZ : center A = ⊥) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (P : Subgroup A)
    (hinv : ∀ a : MulAut A, ((S : Subgroup L).map (modelMap e)).map a.toMonoidHom =
      (S : Subgroup L).map (modelMap e) → P.map a.toMonoidHom = P)
    {B : Type*} [Group B] [Finite B] (b : P ≃* B)
    (c : AbelianSquareControl B) : seedLift e P ≤ M := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQ : Q ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le hU.1)
  have htwo : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hn := seedLift_stable e S hS P hinv
  have hp := seedLift_characteristicTwo e P
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 b).mpr c.selfCentralizingCore)
  have hjoin : HasCharacteristicTwo (seedLift e P ⊔ Q : Subgroup G) := by
    apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
    exact hL.2.relative_local_adjoin_centralizer hL.1 (seedLift_le e P) hQ htwo hn
      ((inf_centralizer_pCoreIn_le_iff 2 _).mpr hp)
  let f := b.toMonoidHom.comp (seedProjection e P)
  have hf : Function.Surjective f := b.surjective.comp (seedProjection_surjective e P)
  have hfc : f.ker ≤ center (seedLift e P) := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective]
    exact seedProjection_ker_central hL e P
  have hfz (x : seedLift e P) (hx : inclusion (seedLift_le e P) x ∈ center L) : f x = 1 := by
    change b (seedProjection e P x) = 1
    rw [seedProjection_kills_center e hZ P x hx, map_one]
  obtain ⟨cover⟩ := hL.2.relative_local_adjoin_normalPowerCover hL.1
    (seedLift_le e P) hQ htwo hn hp f hf hfc hfz
  obtain ⟨d⟩ := h67 U hU _ le_sup_right
    (sup_le ((seedLift_le e P).trans hL.1) hQ) hjoin
  apply le_sup_left.trans (OtherTypes.le_of_blockDecomposition d ?_)
  intro B hB hs hb
  exact Chapter2.ComponentRefinement.M12Exclusion.not_short_of_normalPowerCover c cover
    (B.subgroupOf _) hs (hb.chi.short.of_mulEquiv (subgroupOfEquivOfLe hB).symm)

/-- A two-kernel retains generation by two-elements. -/
theorem primeToResidual_top_of_two_kernel {X Y : Type*} [Group X] [Finite X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hY : primeToResidual 2 Y = ⊤) : primeToResidual 2 X = ⊤ := by
  have hm := map_primeToResidual_of_surjective 2 f hf
  rw [hY] at hm
  have he := congrArg (Subgroup.comap f) hm
  rwa [comap_map_eq_self (le_primeToResidual_of_isPGroup hk), comap_top] at he

/-- Placement and the actual residual condition force V to fix the native seed.
If that seed has trivial automorphism fixer, component escape is impossible. -/
theorem false_of_seedLift_le_M
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* A) (P : Subgroup A)
    (hplace : seedLift e P ≤ M) (hres : primeToResidual 2 P = ⊤)
    (hfix : ∀ a : MulAut A, (∀ p ∈ P, a p = p) → a = 1) : False := by
  have hr : primeToResidual 2 (seedLift e P) = ⊤ :=
    primeToResidual_top_of_two_kernel (seedProjection e P)
      (seedProjection_surjective e P) (seedProjection_ker_two e P) hres
  have hcentral : seedLift e P ≤ centralizer (V : Set G) := by
    let f : seedLift e P →* (L ⊓ M : Subgroup G) :=
      inclusion (le_inf (seedLift_le e P) hplace)
    intro x hx
    have hh := map_primeToResidual_le_of_hom 2 f
    have hxR : (⟨x,hx⟩ : seedLift e P) ∈ primeToResidual 2 (seedLift e P) := by
      rw [hr]
      trivial
    exact (component_intersection_residual hU hL.1
      (mem_map_of_mem (L ⊓ M).subtype (hh (mem_map_of_mem f hxR)))).2
  have hVL := component_normalized h hU hL
  let ρ := L.normalizerMonoidHom.comp (inclusion hVL)
  have hV : V ≤ centralizer (L : Set G) := by
    intro v hv
    have ha : modelAction e (ρ ⟨v,hv⟩) = 1 := by
      apply hfix
      intro p hp
      obtain ⟨x, hx⟩ := seedProjection_surjective e P ⟨p,hp⟩
      have he : modelMap e (inclusion (seedLift_le e P) x) = p := congrArg Subtype.val hx
      rw [← he, modelAction_apply]
      congr 1
      apply Subtype.ext
      change v * (x : G) * v⁻¹ = (x : G)
      rw [hcentral x.property v hv, mul_inv_cancel_right]
    have hb : ρ ⟨v,hv⟩ = 1 := (modelAction_injective hL e) (ha.trans (map_one _).symm)
    intro x hx
    have he := congrArg (fun a : MulAut L => (a ⟨x,hx⟩ : G)) hb
    change v * x * v⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact component_not_le h earlier hU hL
    ((le_centralizer_iff.mpr hV).trans ((Subgroup.centralizer_le_normalizer (V : Set G)).trans h.normalizer_le))

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
