module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicInverter
public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.PResidual.OddImage
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
/-!
# Literal component and Borel maps for the symplectic branch

A supplied genuine equivalence K ≃ Sp₄(F) transports the specified Sylow,
its normalizer, and the Borel quotient to the concrete matrix model. The
actor is conjugation by an element of N_H(K); its kernel remains exactly
C_{N_H(K)}(K). The transported action on the Borel is proved to be that
same conjugation. No faithful ambient-action assumption is introduced.

The source B_C is the embedded two-residual of the literal centralizer
C_B(V). Its ambient-image identity distinguishes it from a two-core.
The odd torus quotient preserves its image, and the Borel order proves
B_C nontrivial once the index-three identity is established.

Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.
The local Thompson/Baumann decomposition and centralizer index are not
asserted here. Simplicity below uses the supplied equivalence to the whole
matrix group; an equivalence only from K/Z(K) would require the earlier
I.1.3 cover argument before applying these declarations.
-/

open Subgroup
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open ActorReduction
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F]
variable (K : Subgroup H) (e : K ≃* Sp F)

/-- The genuine conjugation action transported through the model equivalence. -/
def modelAction : normalizer (K : Set H) →* MulAut (Sp F) :=
  (MulAut.congr e).toMonoidHom.comp K.normalizerMonoidHom

theorem modelAction_ker : (modelAction K e).ker = NormalizerAction.C K := by
  ext a
  change MulAut.congr e (K.normalizerMonoidHom a) = 1 ↔ _
  rw [(MulAut.congr e).map_eq_one_iff]
  change a ∈ K.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]

/-- The given acting subgroup, restricted to the specified Sylow stabilizer. -/
def actors (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S) :
    A →* stabilizerAt S where
  toFun x := ⟨modelAction K e x, hS x x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The Borel as a subgroup of the genuine component K. -/
def localBorel (S : Sylow 2 (Sp F)) : Subgroup K :=
  (borelAt S).comap e.toMonoidHom

variable [Finite F]

/-- The specified model Sylow, transported back to K. -/
def localSylow (S : Sylow 2 (Sp F)) : Sylow 2 K :=
  S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem localSylow_coe (S : Sylow 2 (Sp F)) :
    (localSylow K e S : Subgroup K) = (S : Subgroup (Sp F)).comap e.toMonoidHom := by
  change (S : Subgroup (Sp F)).map e.symm.toMonoidHom = _
  exact map_equiv_eq_comap_symm e.symm _

theorem localBorel_eq_normalizer (S : Sylow 2 (Sp F)) :
    localBorel K e S = normalizer (localSylow K e S : Set K) := by
  rw [show (localSylow K e S : Set K) =
    ((S : Subgroup (Sp F)).comap e.toMonoidHom : Set K) from
      congrArg (fun P : Subgroup K => (P : Set K)) (localSylow_coe K e S)]
  exact comap_normalizer_eq_of_surjective _ e.surjective

/-- Inner alignment with the standard matrix Borel. -/
def atEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : borelAt S ≃* borel (F := F) :=
  (((alignment hF hn S).subgroupMap borel).trans (MulEquiv.subgroupCongr
    (Classical.choose_spec (residualAt_conjugate hF hn S)).2.1)).symm

theorem atEquiv_apply {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (b : borelAt S) :
    (atEquiv hF hn S b : Sp F) = (alignment hF hn S).symm b := rfl

/-- The whole component Borel, with its precise alignment to the matrix Borel. -/
def borelEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : localBorel K e S ≃* borel (F := F) :=
  (MulEquiv.ofBijective (e.toMonoidHom.subgroupComap (borelAt S))
    ⟨fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)),
      e.toMonoidHom.subgroupComap_surjective_of_surjective (borelAt S) e.surjective⟩).trans
    (atEquiv hF hn S)

theorem borelEquiv_apply {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (b : localBorel K e S) :
    (borelEquiv K e hF hn S b : Sp F) = (alignment hF hn S).symm (e b) := rfl

/-- Conjugation on the component Borel; `borelActor_apply` proves compatibility. -/
def borelActor {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (x : A) : MulAut (localBorel K e S) :=
  MulAut.congr (borelEquiv K e hF hn S).symm
    (borelAction (alignActorHom hF hn S (actors K e S A hS x)))

theorem borelActor_apply {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (x : A) (b : localBorel K e S) :
    (borelActor K e hF hn S A hS x b : K) = K.normalizerMonoidHom x b := by
  apply e.injective
  apply (alignment hF hn S).symm.injective
  change (borelEquiv K e hF hn S (borelActor K e hF hn S A hS x b) : Sp F) = _
  simp only [borelActor, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change (alignment hF hn S).symm
    (e (K.normalizerMonoidHom x
      (e.symm ((alignment hF hn S) ((alignment hF hn S).symm (e b)))))) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]

/-- The literal quotient B/O₂(B) is the full rank-two split torus. -/
def quotientEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    localBorel K e S ⧸ pCore 2 (localBorel K e S) ≃* Fˣ × Fˣ :=
  (QuotientGroup.congr _ _ (borelEquiv K e hF hn S)
    (pCore_map_iso 2 _)).trans (quotientTorusEquiv hF)

/-- The quotient map followed by the specified torus equivalence. -/
def characters {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : localBorel K e S →* Fˣ × Fˣ :=
  (quotientEquiv K e hF hn S).toMonoidHom.comp (QuotientGroup.mk' _)

theorem characters_apply {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (b : localBorel K e S) :
    characters K e hF hn S b = borelCharacters (borelEquiv K e hF hn S b) := rfl

theorem characters_ker {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : (characters K e hF hn S).ker = pCore 2 (localBorel K e S) := by
  ext b
  change quotientEquiv K e hF hn S (QuotientGroup.mk' _ b) = 1 ↔ _
  rw [(quotientEquiv K e hF hn S).map_eq_one_iff]
  exact QuotientGroup.eq_one_iff b

theorem characters_surjective {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : Function.Surjective (characters K e hF hn S) :=
  (quotientEquiv K e hF hn S).surjective.comp (QuotientGroup.mk'_surjective _)

theorem characters_actor {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (A : Subgroup (normalizer (K : Set H)))
    (hS : ∀ x ∈ A, (S : Subgroup (Sp F)).map (modelAction K e x).toMonoidHom = S)
    (x : A) (b : localBorel K e S) :
    characters K e hF hn S (borelActor K e hF hn S A hS x b) =
      torusAction hF (alignActorHom hF hn S (actors K e S A hS x))
        (characters K e hF hn S b) := by
  simp only [characters_apply, borelActor, MulAut.congr_apply, MulEquiv.symm_symm,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  exact (torusAction_characters hF _ _).symm


/-- Inclusion of the component Borel in the ambient group. -/
def borelMap (S : Sylow 2 (Sp F)) : localBorel K e S →* H :=
  K.subtype.comp (localBorel K e S).subtype

omit [Finite F] in
theorem borelMap_injective (S : Sylow 2 (Sp F)) :
    Function.Injective (borelMap K e S) :=
  K.subtype_injective.comp (localBorel K e S).subtype_injective

/-- The actual ambient Borel subgroup. -/
def borelIn (S : Sylow 2 (Sp F)) : Subgroup H := (borelMap K e S).range

/-- The literal C_B(V), before taking any residual. -/
def centralizerInBorel (S : Sylow 2 (Sp F)) (V : Subgroup H) :
    Subgroup (localBorel K e S) :=
  (centralizer (V : Set H)).comap (borelMap K e S)

/-- B_C = O²(C_B(V)), as a subgroup of B. -/
def centralizingResidual (S : Sylow 2 (Sp F)) (V : Subgroup H) :
    Subgroup (localBorel K e S) :=
  (pResidual 2 (centralizerInBorel K e S V)).map (centralizerInBorel K e S V).subtype

omit [Finite F] in
theorem centralizerInBorel_map (S : Sylow 2 (Sp F)) (V : Subgroup H) :
    (centralizerInBorel K e S V).map (borelMap K e S) =
      borelIn K e S ⊓ centralizer (V : Set H) := by
  rw [centralizerInBorel, map_comap_eq]
  rfl

variable [Finite H]

omit [Finite F] in
theorem centralizingResidual_map (S : Sylow 2 (Sp F)) (V : Subgroup H) :
    (centralizingResidual K e S V).map (borelMap K e S) =
      (pResidual 2 ↥(borelIn K e S ⊓ centralizer (V : Set H))).map
        (borelIn K e S ⊓ centralizer (V : Set H)).subtype := by
  rw [centralizingResidual, map_embedded_pResidual, centralizerInBorel_map]

variable [CharP F 2]

include e in
omit [Finite H] in
theorem component_simple {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsSimpleGroup K := by
  let := SimpleQuotients.isSimpleGroup_of_card_eq_two_pow hn hF
  exact (e.trans EvenProjective.equiv).isSimpleGroup

omit [Finite H] [CharP F 2] in
theorem twoCore_index {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    (pCore 2 (localBorel K e S)).index = (2^n - 1)^2 := by
  rw [← characters_ker K e hF hn S, index_ker,
    MonoidHom.range_eq_top.mpr (characters_surjective K e hF hn S), card_top,
    Nat.card_prod, Nat.card_units, hF, pow_two]

omit [CharP F 2] in
theorem residual_index {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (V : Subgroup H) :
    (centralizingResidual K e S V ⊔ pCore 2 (localBorel K e S)).index =
      (centralizerInBorel K e S V ⊔ pCore 2 (localBorel K e S)).index := by
  rw [← characters_ker K e hF hn S]
  exact embedded_twoResidual_sup_ker_index (characters K e hF hn S)
    (characters_surjective K e hF hn S) (Nat.coprime_two_left.mp (torus_odd hF)) _

omit [Finite H] [CharP F 2] in
theorem residual_ne_bot {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (V : Subgroup H)
    (hi : (centralizingResidual K e S V ⊔ pCore 2 (localBorel K e S)).index = 3) :
    centralizingResidual K e S V ≠ ⊥ := by
  intro he
  rw [he, bot_sup_eq, twoCore_index K e hF hn.le S] at hi
  have hpow : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  have hsub : 3 ≤ 2^n - 1 := by omega
  have hs := Nat.mul_self_le_mul_self hsub
  norm_num [← pow_two, hi] at hs

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
