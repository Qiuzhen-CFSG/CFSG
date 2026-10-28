module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds

/-!
# The Sylow subgroup at mu in Held's terminal argument

The actual intersection C_G(pi) intersect C_G(mu) is S<mu',xi>, of order 64.
Choose a Sylow two-subgroup of C_G(mu) containing this intersection. Under
pi--mu fusion its ambient image has order 128 and is not contained in the
original displayed Sylow D. Their join therefore strictly contains D.

The binary normal forms identify the whole local intersection. Sylow existence
is applied inside the actual C_G(mu), and its order follows by conjugating
C_G(pi) to C_G(mu). No order or normality of the join is asserted here.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private abbrev MuCode := BaseCode × Fin 2 × Fin 2
private def muWord (a : MuCode) : H :=
  elementaryWord 1 a.1 * mup ^ a.2.1.val * xi ^ a.2.2.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem muWord_injective : Function.Injective muWord := by decide +kernel

private theorem muWord_commutes : ∀ a, muWord a * mu = mu * muWord a := by decide +kernel

private def muWordLift (a : MuCode) : centralizer ({mu} : Set H) :=
  ⟨muWord a, mem_centralizer_singleton_iff.mpr (muWord_commutes a)⟩

private theorem muWordLift_bijective : Function.Bijective muWordLift := by
  have hi : Function.Injective muWordLift := fun a b h =>
    muWord_injective (congrArg Subtype.val h)
  apply hi.bijective_of_nat_card_le
  rw [centralizer_mu_card]
  simp [MuCode, BaseCode]

/-- The entire local mu-centralizer is the source subgroup S<mu',xi>. -/
public theorem terminal_model_mu_core :
    centralizer ({mu} : Set H) = modelS ⊔ zpowers mup ⊔ zpowers xi := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := muWordLift_bijective.surjective ⟨x, hx⟩
    have he : muWord a = x := congrArg Subtype.val ha
    rw [← he, muWord]
    apply mul_mem
    · apply mul_mem
      · exact (le_sup_left.trans le_sup_left : modelS ≤
          modelS ⊔ zpowers mup ⊔ zpowers xi) ((mem_elementary 1 _).mpr ⟨a.1, rfl⟩)
      · exact (le_sup_right.trans le_sup_left : zpowers mup ≤
          modelS ⊔ zpowers mup ⊔ zpowers xi) (pow_mem (mem_zpowers _) _)
    · exact (le_sup_right : zpowers xi ≤ modelS ⊔ zpowers mup ⊔ zpowers xi)
        (pow_mem (mem_zpowers _) _)
  · apply sup_le (sup_le (elementary_le_centralizer_mu 1) ?_) ?_
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr (by decide +kernel)
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr (by decide +kernel)

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The ambient centralizer at the original model image of mu. -/
public abbrev terminalMuCentralizer : Subgroup G := centralizer ({D.a10NoncentralInvolution e} : Set G)
/-- The actual common subgroup of the two involution centralizers. -/
@[expose] public noncomputable def terminalMuCore : Subgroup G := D.centralizer ⊓ terminalMuCentralizer D e
/-- A Sylow subgroup of C_G(mu), included in G. -/
@[expose] public noncomputable def terminalMuSylowImage (P : Sylow 2 (terminalMuCentralizer D e)) : Subgroup G :=
  (P : Subgroup (terminalMuCentralizer D e)).map (terminalMuCentralizer D e).subtype
/-- Held's K=<D,D_mu>, with the actual Sylow subgroup at mu supplied. -/
@[expose] public noncomputable def terminalJoin (P : Sylow 2 (terminalMuCentralizer D e)) : Subgroup G :=
  ambientD D e ⊔ terminalMuSylowImage D e P

public theorem terminalMuCore_eq : terminalMuCore D e =
    ambientElementary D e 1 ⊔ zpowers (D.a10ModelEmbedding e mup) ⊔
      zpowers (D.a10ModelEmbedding e xi) := by
  change D.centralizer ⊓ centralizer ({D.a10NoncentralInvolution e} : Set G) = _
  rw [← ambient_centralizer_mu_map, terminal_model_mu_core, Subgroup.map_sup, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

public theorem terminalMuCore_card : Nat.card (terminalMuCore D e) = 64 :=
  ambient_intersection_card D e

public theorem terminalMuSylowImage_le (P : Sylow 2 (terminalMuCentralizer D e)) :
    terminalMuSylowImage D e P ≤ terminalMuCentralizer D e :=
  map_subtype_le _

public theorem terminal_exists_mu_sylow :
    ∃ P : Sylow 2 (terminalMuCentralizer D e), terminalMuCore D e ≤ terminalMuSylowImage D e P := by
  let Q := (terminalMuCore D e).subgroupOf (terminalMuCentralizer D e)
  have hle : terminalMuCore D e ≤ terminalMuCentralizer D e := inf_le_right
  have hQ : Nat.card Q = 2 ^ 6 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, terminalMuCore_card]
    norm_num
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hQ).exists_le_sylow
  refine ⟨P, ?_⟩
  have hmap := map_mono (f := (terminalMuCentralizer D e).subtype) hP
  rwa [map_subgroupOf_eq_of_le hle] at hmap

public theorem terminalMuSylowImage_card [Finite G]
    (hmu : IsConj D.z (D.a10NoncentralInvolution e)) (P : Sylow 2 (terminalMuCentralizer D e)) :
    Nat.card (terminalMuSylowImage D e P) = 128 := by
  rw [terminalMuSylowImage, card_map_of_injective Subtype.val_injective,
    Sylow.card_eq_multiplicity, centralizer_card_of_isConj D hmu]
  decide +kernel

public theorem terminalMuSylowImage_not_le_ambientD [Finite G]
    (hmu : IsConj D.z (D.a10NoncentralInvolution e)) (P : Sylow 2 (terminalMuCentralizer D e)) :
    ¬ terminalMuSylowImage D e P ≤ ambientD D e := by
  intro h
  have hDH : ambientD D e ≤ D.centralizer := by
    rw [← D.a10ModelEmbedding_range e]
    exact map_le_range _ _
  have hle : terminalMuSylowImage D e P ≤ terminalMuCore D e :=
    le_inf (h.trans hDH) (terminalMuSylowImage_le D e P)
  have hc := card_le_of_le hle
  rw [terminalMuSylowImage_card D e hmu P, terminalMuCore_card] at hc
  omega

public theorem terminal_ambientD_lt_join [Finite G]
    (hmu : IsConj D.z (D.a10NoncentralInvolution e)) (P : Sylow 2 (terminalMuCentralizer D e)) :
    ambientD D e < terminalJoin D e P :=
  left_lt_sup.mpr (terminalMuSylowImage_not_le_ambientD D e hmu P)

/-- The actual subgroup <pi,mu> used for the conjugation action of K. -/
@[expose] public noncomputable def terminalFour : Subgroup G :=
  closure ({D.z, D.a10NoncentralInvolution e} : Set G)

public theorem terminalFour_centralizer :
    centralizer (terminalFour D e : Set G) = terminalMuCore D e := by
  rw [terminalFour, centralizer_closure]
  ext x
  simp only [terminalMuCore, mem_inf, mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

public theorem terminalFour_le_S [Finite G] : terminalFour D e ≤ ambientElementary D e 1 := by
  rw [terminalFour, closure_le]
  rintro x (rfl | rfl)
  · rw [← D.a10ModelEmbedding_central e]
    exact mem_map_of_mem _ (pi_mem_elementary 1)
  · exact mem_map_of_mem _ (mu_mem_elementary 1)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
