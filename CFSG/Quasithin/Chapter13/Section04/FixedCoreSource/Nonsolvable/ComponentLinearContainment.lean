module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentDoubled
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortBlock
public import Theory.Representation.PSL3Two.DoubledSylowPoint
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Original residual containment for doubled linear-three components

A Sylow subgroup of the selected K lies in the original T. The fixed-line
generator therefore determines a Sylow-fixed nonzero point of the literal
moved orbit. Its doubled natural marking gives an S₄ point centralizer,
and hence a cubic in K ∩ N_G(L), without assuming L₁ ≤ K.

When L/O₂(L) is ordinary A₆, taking the cubic residual of that intersection
places its cubic inside L. Thus K ∩ C_L(z) has order divisible by three.
It is normal in C_L(z), whose two-core quotient is S₃. The quotient by
K ∩ C_L(z) is consequently a two-group, proving L₁ = O²(C_L(z)) ≤ K.
The earlier reciprocal-residual theorem now applies with its literal maps.

A short block with the five-dimensional augmentation marking is already
ordinary A₆. The final consumer therefore excludes the doubled row from
shortness alone, discharging the old containment premise internally.
The augmentation Baumann/short-block alternative, covered original row,
other module exclusions and 13.4.10–17 assembly remain with
qt-d-1341-nonsolvable-source. No four-dimensional NaturalSetup or stronger
ambient exclusion is assumed. Earlier 12.2/13.3 inputs retain their existing
producers and final discharge with qt-d-1341-fixed-core-source; universal
nonsolvability remains required separately at both escaping weights.

Source: Aschbacher–Smith, 13.4.10(2–4), printed pp.908–909;
13.2.2(7), printed pp.877–878, is the remaining block alternative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- A cubic in the reciprocal centralizer suffices for the original ordinary
residual containment. Relative normality is in C_G(z), not in G. -/
theorem ordinary_firstResidual_le_of_reciprocal_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hthree : 3 ∣ Nat.card (K ⊓ normalizer (L : Set G) : Subgroup G)) :
    Solvable.firstCentralizerResidual L z.val ≤ K := by
  let H := centralizer ({z.val} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := K ⊓ M
  let R := (primeToResidual 3 B).map B.subtype
  have hRL : R ≤ L := by
    rw [←original_normalizer_residual h structural eL]
    exact embedded_primeToResidual_mono 3 inf_le_right
  have hRK : R ≤ K := (map_subtype_le _).trans inf_le_left
  have hRC : R ≤ C := le_inf hRL (hRK.trans hKz)
  have hthreeR : 3 ∣ Nat.card R := by
    rw [card_map_of_injective B.subtype_injective]
    have hd : 3 ∣ Nat.card B := hthree
    rw [←(primeToResidual 3 B).card_mul_index] at hd
    exact (Nat.prime_three.dvd_mul.mp hd).resolve_right
      (Nat.prime_three.coprime_iff_not_dvd.mp (primeToResidual_index_coprime 3))
  let N := K.subgroupOf C
  let : N.Normal := normal_subgroupOf_of_le_normalizer (inf_le_right.trans hHN)
  let f : R →* N := (inclusion hRC).codRestrict N (fun r => hRK r.property)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : N => x.val.val) hab)
  have hthreeN : 3 ∣ Nat.card N := hthreeR.trans (card_dvd_of_injective f hf)
  have hc : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) := by
    rw [Solvable.centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eC⟩ := Solvable.component_centralizer_quotient D m hc z hz
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  have hcard : Nat.card C = 2 ^ (n+1) * 3 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 C),
      Nat.card_congr eC.toEquiv,Nat.card_perm,Nat.card_fin,hn,pow_succ]
    norm_num [Nat.factorial]
    ring
  have hp : IsPGroup 2 (C ⧸ N) := by
    apply IsPGroup.of_card_dvd_pow (n := n+1)
    apply (Nat.mul_dvd_mul_iff_right (by decide : 0 < 3)).mp
    rw [←hcard,card_eq_card_quotient_mul_card_subgroup N]
    exact Nat.mul_dvd_mul_left _ hthreeN
  have hr : pResidual 2 C ≤ N := sInf_le ⟨inferInstance,hp⟩
  have he := core_component_point_twoResidual D m eL z hz
  rw [←he]
  rintro k ⟨c,hc,rfl⟩
  exact hr hc

private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])

/-- The doubled moved orbit supplies a cubic in the literal reciprocal
centralizer, before any containment of L₁ in K is known. -/
theorem doubled_reciprocal_cubic
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    3 ∣ Nat.card (K ⊓ normalizer (L : Set G) : Subgroup G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hKz hTK hKM
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  have hSw : (S : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set G) := by
    intro k hk
    have hkd : k ∈ centralizer ({m.constant.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_omegaOneCenterAmbient_iff _ _).mp
        (m.constant_mem_central_four h structural).2 |>.2.2 k (hS hk)
    exact (hC.le ⟨map_subtype_le _ hk,hkd⟩).2
  obtain ⟨f,hf,_⟩ := BinaryLinearThree.doubled_point_centralizer_of_sylow
    K U (normalizer_commutator_ge_right _ _) eK e he w hw S hSw
  have hd := card_dvd_of_surjective f hf
  rw [Nat.card_perm,Nat.card_fin] at hd
  have hc : K ⊓ normalizer (L : Set G) = K ⊓ centralizer ({w.val} : Set G) := by
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    exact hC
  rw [hc]
  exact (by decide : 3 ∣ Nat.factorial 4).trans hd

/-- The original ordinary-A₆ branch contains L₁ in a doubled linear-three
component; the reciprocal residual equality follows with the same embeddings. -/
theorem ordinary_doubled_component_residuals
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    Solvable.firstCentralizerResidual L z.val ≤ K ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val := by
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have h3 := doubled_reciprocal_cubic h₀ h structural D m hzT hz1 hKz hTK hKM eK e he
  have hJK := ordinary_firstResidual_le_of_reciprocal_cubic h structural D m eL z hzL hKz hHN h3
  exact ⟨hJK,component_reciprocal_residual_of_containment h structural m z.val hKz hHN eL hJK⟩

/-- The genuine five-dimensional short-block branch excludes the doubled row
without assuming residual containment or a reciprocal quotient map. -/
theorem core_block_excludes_doubled_without_containment
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  obtain ⟨eL⟩ := Solvable.ordinary_of_short_core_marking D m hb
  have hJK := (ordinary_doubled_component_residuals h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he).1
  exact core_block_excludes_actual_doubled_component h₀ h structural D m z hzT hzL
    hKz hHN hTK hKM hJK hb eK e he

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
