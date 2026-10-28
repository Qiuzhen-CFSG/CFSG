module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiRemoteCenters
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonlinearCoreGeneration

/-!
# Escaping incoming subgroups at the actual small Suzuki vertex

Two subgroups in distinct incoming cores, both escaping the middle core,
have nontrivial images in distinct Sylows of the order-twenty quotient.
Their join cannot be a two-group. Its index is therefore coprime to five,
which proves transitivity on the literal five-neighbor action. This does
not assert that the two subgroups generate the full Suzuki quotient.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Escaping subgroups in the two original incoming cores act transitively
on the neighborhood of the marked small-Suzuki vertex. -/
theorem source_small_suzuki_two_core_escape_transitive
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    {z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hne : z ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (D B : Subgroup (G₀ L S))
    (hDm : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hBz : B ≤ Q (reducedFamily L S) z)
    (hD : ¬ D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hB : ¬ B ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    : ∀ v, (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v →
      ∃ g ∈ D ⊔ B,
        g • base (reducedFamily L S) (!i) = v := by
  let F := reducedFamily L S
  let A := star L S i
  let y := base F i
  let m := base F (!i)
  let E := D ⊔ B
  let H := E ⊔ Q F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  have hkQ : f.ker = (Q F y).subgroupOf A := by
    rw [hk,←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hmA : Q F m ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hzA : Q F z ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hyA : Q F y ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have haA : D ≤ A := hDm.trans hmA
  have hcA : B ≤ A := hBz.trans hzA
  have hEA : E ≤ A := sup_le haA hcA
  have hHA : H ≤ A := sup_le hEA hyA
  obtain ⟨P,hP,_,_⟩ := source_common_sylow_core_index h i e T hT
  obtain ⟨U,hU,_,_⟩ := source_common_sylow_core_index h i e R hR
  have hgen := star_three_core_generation h i hyz hne T R hT hR
  have hPU : (P : Subgroup (SuzukiMatrixGroup 0)) ⊔ U = ⊤ := by
    have he : (Q F m).subgroupOf A ⊔ (Q F z).subgroupOf A ⊔ (Q F y).subgroupOf A = ⊤ := by
      apply map_injective A.subtype_injective
      rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hmA,
        map_subgroupOf_eq_of_le hzA,map_subgroupOf_eq_of_le hyA,
        ←MonoidHom.range_eq_map,range_subtype]
      exact hgen.symm
    have hh := congrArg (Subgroup.map f) he
    rw [Subgroup.map_sup,Subgroup.map_sup,hP,hU,←hkQ,Subgroup.map_ker_self,
      sup_bot_eq,Subgroup.map_top_of_surjective _ hf] at hh
    exact hh
  have hnePU : P ≠ U := by
    intro he
    rw [he,sup_idem] at hPU
    exact (suzuki_rankOneSylowFacts 0 U).proper.not_ge (hPU ▸ U.toSubgroup.le_normalizer)
  have himage_ne (J : Subgroup (G₀ L S)) (hJA : J ≤ A) (hJ : ¬ J ≤ Q F y) :
      (J.subgroupOf A).map f ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (J.subgroupOf A)).mp he
    rw [hkQ] at hh
    exact hJ (fun t ht => hh (show (⟨t,hJA ht⟩ : A) ∈ J.subgroupOf A from ht))
  let K := H.subgroupOf A
  have hkerK : f.ker ≤ K := by
    rw [hkQ]
    exact fun _ ht => mem_sup_right ht
  have hnot : ¬ IsPGroup 2 (K.map f) := by
    intro hp
    obtain ⟨J,hJ⟩ := hp.exists_le_sylow
    have haP : (D.subgroupOf A).map f ≤ P := hP ▸ map_mono (subgroupOf_mono A hDm)
    have hcU : (B.subgroupOf A).map f ≤ U := hU ▸ map_mono (subgroupOf_mono A hBz)
    have haJ : (D.subgroupOf A).map f ≤ J :=
      (map_mono (subgroupOf_mono A (show D ≤ H from le_sup_left.trans le_sup_left))).trans hJ
    have hcJ : (B.subgroupOf A).map f ≤ J :=
      (map_mono (subgroupOf_mono A (show B ≤ H from le_sup_right.trans le_sup_left))).trans hJ
    have hPJ : P = J := smallSuzuki_sylow_eq_of_inf_ne_bot P J (by
      intro he
      exact himage_ne D haA hD (bot_unique ((le_inf haP haJ).trans_eq he)))
    have hUJ : U = J := smallSuzuki_sylow_eq_of_inf_ne_bot U J (by
      intro he
      exact himage_ne B hcA hB (bot_unique ((le_inf hcU hcJ).trans_eq he)))
    exact hnePU (hPJ.trans hUJ.symm)
  have hcop : Nat.Coprime 5 K.index := by
    rw [←K.index_map_eq hf hkerK]
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    rintro ⟨n,hn⟩
    have hh := (K.map f).card_mul_index
    rw [suzukiZero_card,hn] at hh
    have hd : Nat.card (K.map f) ∣ 2^2 := ⟨n,by nlinarith⟩
    exact hnot (IsPGroup.of_card_dvd_pow hd)
  let P₀ : Sylow 2 (SuzukiMatrixGroup 0) := T.mapSurjective (f := f) hf
  have hPT : (P₀ : Subgroup (SuzukiMatrixGroup 0)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨T₀,hT₀⟩ := base_star_sylow_normalizer h i
  have hTfix : (T : Subgroup A).map A.subtype ≤ stabilizer F m := by
    rw [hT]
    exact sup_le (Q_le_stabilizer F _) (((source_Z_Q_U (reduced_triple h) y).2.trans
      (ballKernel_one_le_edge F hadj)).trans inf_le_right)
  have heT : T = T₀ := sylow_le_normalizer_eq T₀ T (by
    rw [←hT₀]
    exact fun t ht => hTfix (mem_map_of_mem A.subtype ht))
  obtain ⟨p,hp,_⟩ := CommutingOneProfile.small_suzuki_orbits P₀
  have hstab : (MulAction.stabilizer (SuzukiMatrixGroup 0) p).comap f =
      MulAction.stabilizer A m := by
    rw [←hp]
    change (normalizer ((P₀ : Subgroup (SuzukiMatrixGroup 0)) : Set (SuzukiMatrixGroup 0))).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf,hPT,Sylow.coe_coe,heT,←hT₀]
    rfl
  have hidx : (MulAction.stabilizer A m).index = 5 := by
    rw [←hstab,index_comap_of_surjective _ hf,MulAction.index_stabilizer_of_transitive,
      suzukiOvoid_card]
    norm_num
  let X := MulAction.orbit A m
  have hcard : Nat.card X = 5 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A m),←index_eq_card,hidx]
  let : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : MulAction.IsPretransitive K X :=
    MulAction.isPretransitive_of_prime_card_of_coprime_index (by decide) hcard K hcop
  have hnE : E ≤ normalizer (Q F y : Set (G₀ L S)) :=
    (hEA.trans (star_le_stabilizer i)).trans (stabilizer_normalizes_Q F y)
  intro v hv
  obtain ⟨t,ht,htm⟩ := star_locally_transitive h i hadj hv
  let xm : X := ⟨m,MulAction.mem_orbit_self m⟩
  let xv : X := ⟨v,⟨(⟨t,ht⟩ : A),htm⟩⟩
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq K xm xv
  have hum : ((u : A) : G₀ L S) • m = v := congrArg Subtype.val hu
  have huH : ((u : A) : G₀ L S) ∈ H := u.property
  have hu' : ((u : A) : G₀ L S) ∈ (E : Set (G₀ L S)) * (Q F y : Set (G₀ L S)) := by
    rw [←coe_mul_of_left_le_normalizer_right E (Q F y) hnE]
    exact huH
  obtain ⟨g,hg,q,hq,he⟩ := hu'
  have hqm : q • m = m := ((source_Z_Q_U (reduced_triple h) y).2.trans
    ((ballKernel_one_le_edge F hadj).trans inf_le_right)) hq
  refine ⟨g,hg,?_⟩
  change g*q = ((u : A) : G₀ L S) at he
  rw [←he,mul_smul,hqm] at hum
  exact hum

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
