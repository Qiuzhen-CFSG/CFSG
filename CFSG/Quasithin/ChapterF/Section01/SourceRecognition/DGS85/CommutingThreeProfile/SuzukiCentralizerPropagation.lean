module
public import Theory.SpecificGroups.Suzuki.OddCenterRigidity
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiComplementTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearComplementTransitivity
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MarkedComplementIndex

/-!
# Centralizer propagation at the marked linear and Suzuki vertices

Let J be a subgroup of the incoming vertex core normalized by the full
edge complement. If J escapes the current vertex core, its linear image
is the whole root group, while its Suzuki image contains the full root
center. An odd actor centralizing J then acts trivially on the Suzuki
quotient, hence fixes every actual neighbor. At a linear vertex, the
root orbit gives the same conclusion when the actor fixes the chosen exit.

The arbitrary-edge versions conjugate the original groups, quotient maps,
and actions together. These statements concern the full permutation
kernel; it is never identified with the vertex two-core. The application
in SuzukiTorusCentralizer follows the selected complement-fixed eight-path.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed p.189, the torus-centralizer step.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- An odd actor centralizing an escaping complement-invariant incoming core fixes the full Suzuki star. -/
theorem suzuki_complement_invariant_centralizer_kernel
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (J K D : Subgroup (G₀ L S))
    (hJ : J ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hesc : ¬ J ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hK : K ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hcomp : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S))).IsComplement'
      (K.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        stabilizer (reducedFamily L S) (base (reducedFamily L S) i))))
    (hoddK : Odd (Nat.card K)) (hnorm : K ≤ normalizer (J : Set (G₀ L S)))
    (hD : D ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) i))
    (hoddD : Odd (Nat.card D)) (hDJ : D ≤ centralizer (J : Set (G₀ L S))) :
    D ≤ ballKernel (reducedFamily L S) (base (reducedFamily L S) i) 1 := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F (base F (!i)) ⊓ stabilizer F (base F i)
  let e' := (originalQuotient h i).symm.trans e
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (hD.trans inf_le_right)) (inclusion_injective _)
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hJA : J ≤ A := hJ.trans ((le_sup_left.trans hT.ge).trans (map_subtype_le _))
  have hk : q.ker = (Q F (base F i)).subgroupOf A := by
    have he : q.ker = pCore 2 A := by
      ext a
      change e' (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff _ e'.injective]
      exact QuotientGroup.eq_one_iff a
    rw [he,←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  obtain ⟨P,hP,hcover⟩ := source_quotient_edge_complement_supplement h i hadj e
    (K.subgroupOf E) hcomp ((Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv).symm ▸ hoddK)
  rw [map_subgroupOf_eq_of_le hK] at hcover
  let I := (J.subgroupOf A).map q
  have hIP : I ≤ P := by
    have hp : IsPGroup 2 I := (((isPGroup_pCoreIn 2 _).to_le hJ).comap_subtype).map q
    have hN : I ≤ normalizer (P : Set (SuzukiMatrixGroup n)) := by
      apply map_le_iff_le_comap.mpr
      rw [hP]
      exact fun a ha => Q_le_stabilizer F _ (hJ ha)
    rw [←inf_eq_left.mpr hN,hp.inf_normalizer_sylow P]
    exact inf_le_right
  have hIne : I ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (J.subgroupOf A)).mp he
    rw [hk] at hh
    exact hesc (fun j hj => hh (show (⟨j,hJA hj⟩ : A) ∈ J.subgroupOf A from hj))
  have hnA : K.subgroupOf A ≤ normalizer (J.subgroupOf A : Set A) := by
    intro a ha
    exact le_normalizer_comap A.subtype (hnorm ha)
  have hnI : (K.subgroupOf A).map q ≤ normalizer (I : Set (SuzukiMatrixGroup n)) :=
    (map_mono hnA).trans ((J.subgroupOf A).le_normalizer_map q)
  have hZI := suzuki_center_le_of_supplement_invariant hn (MulEquiv.refl _) P I
    ((K.subgroupOf A).map q) hIP hIne hcover hnI
  have hDN : D ≤ normalizer (A : Set (G₀ L S)) :=
    (hD.trans inf_le_right).trans (star_normalized_by_vertex h i)
  let ρ : D →* MulAut (SuzukiMatrixGroup n) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 A)).comp (A.normalizerMonoidHom.comp (inclusion hDN)))
  have hρ (d : D) (a : A) :
      ρ d (q a) = q (A.normalizerMonoidHom (inclusion hDN d) a) := by
    change e' ((quotientAut (pCore 2 A) (A.normalizerMonoidHom (inclusion hDN d)))
      (e'.symm (e' (QuotientGroup.mk' (pCore 2 A) a)))) = _
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hρone (d : D) : ρ d = 1 := by
    apply suzuki_odd_aut_eq_one_of_fixing_sylow_center hn (MulEquiv.refl _) P
    · exact (hoddD.of_dvd_nat (orderOf_dvd_natCard d)).of_dvd_nat (orderOf_map_dvd ρ d)
    · intro z hz
      obtain ⟨a,ha,rfl⟩ := hZI hz
      rw [hρ]
      apply congrArg q
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hDJ d.property a ha).symm
  intro d hd z hz
  rcases (mem_ball_one F _ _).mp hz with hz | rfl
  · obtain ⟨a,ha,haz⟩ := star_locally_transitive h i hadj hz
    let aA : A := ⟨a,ha⟩
    let dD : D := ⟨d,hd⟩
    let bA := A.normalizerMonoidHom (inclusion hDN dD) aA
    have he : q bA = q aA := by rw [←hρ,hρone]; rfl
    have hb : bA * aA⁻¹ ∈ q.ker := by
      change q (bA * aA⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [hk] at hb
    have hfix := (((source_Z_Q_U (reduced_triple h) _).2.trans
      (ballKernel_one_le_edge F hz)).trans inf_le_right) hb
    change (d*a*d⁻¹*a⁻¹) • z = z at hfix
    have hdy : d⁻¹ • base F (!i) = base F (!i) := (hD (D.inv_mem hd)).1
    rw [←haz,mul_smul,mul_smul,mul_smul,inv_smul_smul,hdy] at hfix
    rwa [haz] at hfix
  · exact (hD hd).2

/-- The Suzuki centralizer propagation through the literal conjugation of an arbitrary edge. -/
theorem suzuki_complement_invariant_centralizer_kernel_at
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    {a x : Vertex (reducedFamily L S)} (ha : a.type = i)
    (hax : (graph (reducedFamily L S)).Adj a x)
    (J K D : Subgroup (G₀ L S)) (hJ : J ≤ Q (reducedFamily L S) x)
    (hesc : ¬ J ≤ Q (reducedFamily L S) a)
    (hK : K ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)
    (hcomp : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S))).IsComplement'
        (K.subgroupOf (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)))
    (hoddK : Odd (Nat.card K)) (hnorm : K ≤ normalizer (J : Set (G₀ L S)))
    (hD : D ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)
    (hoddD : Odd (Nat.card D)) (hDJ : D ≤ centralizer (J : Set (G₀ L S))) :
    D ≤ ballKernel (reducedFamily L S) a 1 := by
  let F := reducedFamily L S
  obtain ⟨g,hga,hgx⟩ := incident_common_translate F hax.2
  have hx : x.type = !i := Bool.eq_not_iff.mpr (ha ▸ hax.1.symm)
  rw [ha] at hga
  rw [hx] at hgx
  have hga' : g⁻¹ • a = base F i := by rw [←hga,inv_smul_smul]
  have hgx' : g⁻¹ • x = base F (!i) := by rw [←hgx,inv_smul_smul]
  let c := (MulAut.conj g⁻¹).toMonoidHom
  let J' := J.map c
  let K' := K.map c
  have hJ' : J' ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) hJ
    change J' ≤ (Q F x).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Q_translate F,hgx'] at hh
  have hesc' : ¬ J' ≤ Q F (base F i) := by
    intro hh
    apply hesc
    have hQ : Q F (base F i) = (Q F a).map c := by
      rw [←Q_translate F,hga']
    rw [hQ] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have transport_edge (U : Subgroup (G₀ L S))
      (hU : U ≤ stabilizer F x ⊓ stabilizer F a) : U.map c ≤ stabilizer F (base F (!i)) ⊓ stabilizer F (base F i) := by
    rintro t ⟨d,hd,rfl⟩
    have hdx : d • x = x := (hU hd).1
    have hda : d • a = a := (hU hd).2
    constructor
    · change (g⁻¹*d*(g⁻¹)⁻¹) • base F (!i) = base F (!i)
      rw [inv_inv,mul_smul,mul_smul,hgx,hdx,hgx']
    · change (g⁻¹*d*(g⁻¹)⁻¹) • base F i = base F i
      rw [inv_inv,mul_smul,mul_smul,hga,hda,hga']
  have hK' := transport_edge K hK
  let D' := D.map c
  have hD' := transport_edge D hD
  have hadj : (graph F).Adj (base F (!i)) (base F i) :=
    ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
  have hc : Nat.card K' = Nat.card K := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcomp' := source_edge_complement_transfer h hax.symm hadj
    (K.subgroupOf (stabilizer F x ⊓ stabilizer F a)) hcomp K' hK'
    (hc.symm ▸ hoddK) (hc.trans (Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv).symm)
  have hnorm' : K' ≤ normalizer (J' : Set (G₀ L S)) :=
    (map_mono hnorm).trans (J.le_normalizer_map c)
  have hDJ' : D' ≤ centralizer (J' : Set (G₀ L S)) :=
    (map_mono hDJ).trans (by simpa only [J',Subgroup.coe_map] using map_centralizer_le_centralizer_image (J : Set (G₀ L S)) c)
  have hker := suzuki_complement_invariant_centralizer_kernel h i hn e T hT J' K' D'
    hJ' hesc' hK' hcomp' (hc.symm ▸ hoddK) hnorm' hD'
    ((show Nat.card D' = Nat.card D from card_map_of_injective (MulAut.conj g⁻¹).injective).symm ▸ hoddD) hDJ'
  have he : ballKernel F (base F i) 1 = (ballKernel F a 1).map c := by
    rw [←ballKernel_translate F,hga']
  rw [he] at hker
  exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hker

open scoped MatrixGroups
/-- The linear root orbit forces an odd centralizing path actor into the full local kernel. -/
theorem linear_complement_invariant_centralizer_kernel_at
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {a x z : Vertex (reducedFamily L S)} (ha : a.type = i)
    (hax : (graph (reducedFamily L S)).Adj a x)
    (haz : (graph (reducedFamily L S)).Adj a z) (hzx : z ≠ x)
    (J K D : Subgroup (G₀ L S)) (hJ : J ≤ Q (reducedFamily L S) x)
    (hesc : ¬ J ≤ Q (reducedFamily L S) a)
    (hK : K ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)
    (hcomp : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S))).IsComplement'
        (K.subgroupOf (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)))
    (hoddK : Odd (Nat.card K)) (hnorm : K ≤ normalizer (J : Set (G₀ L S)))
    (hDK : D ≤ K) (hDz : D ≤ stabilizer (reducedFamily L S) z)
    (hDJ : D ≤ centralizer (J : Set (G₀ L S))) :
    D ≤ ballKernel (reducedFamily L S) a 1 := by
  let F := reducedFamily L S
  obtain ⟨_,ht⟩ := linear_complement_invariant_transitive_at h i e T hT ha hax
    J K hJ hesc hK hcomp hoddK hnorm
  intro d hd v hv
  rcases (mem_ball_one F a v).mp hv with hv | rfl
  · by_cases he : v = x
    · subst v; exact (hK (hDK hd)).1
    obtain ⟨j,hj,hjz⟩ := ht z v haz hv hzx he
    rw [←hjz,←mul_smul,(hDJ hd j hj).symm,mul_smul,hDz hd]
  · exact (hK (hDK hd)).2
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
