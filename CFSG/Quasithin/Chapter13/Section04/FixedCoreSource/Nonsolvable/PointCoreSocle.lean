module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalResidualWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFullQuotient
public import Theory.Representation.BinaryConjugationCoordinates.SupplementSpaces
public import Theory.Representation.PSL3Two.FanoSocleFlags

/-!
# The point-core socle row of the original nonsolvable pair

For H₀=H₂ join L₂T with the actual point-core module for its L₃(2)
component, the same quotient marking sends H₂, L₂T and T to the point
parabolic, line parabolic and flag Sylow. The centralizing two-core
supplement transports the Fano fixed spaces, seed commutators and socle
to the full original H₀ action on V₀=⟨Ω₁Z(T)^H₀⟩.

Consequently C_Z(L₂T) lies in Soc(V₀) and [Z,O²(H₂)], while C_Z(H₂)
lies in neither Soc(V₀) nor [Z,L₂]. The original five-dimensional weight
test forces z to have weight two. In both natural component rows C_V(L)
lies in V_K. In the five-dimensional ordinary A₆ row the same fixed
line has weight four in V_K: original outside-parabolic uniqueness
identifies the reciprocal weight test with H₂, rather than changing the
chosen actor or quotient map.

This proves the point-core realization of 13.4.14(2ii), including both
recognized component rows. The line-core and semisimple H₀ rows, both-weight
uniqueness, mixed/product reciprocal exclusions and final graph argument
remain with the nonsolvable assembly. Earlier Structural1222, 13.3.2,
original M=LT and the independent LargeDistanceInput remain explicit.
The point-core marking is one branch of the already proved
Amalgam.original_pair_linear_whole_module, not an additional conclusion
assumed in the original nonsolvable-centralizer theorem.

Source: Aschbacher–Smith, 13.4.14, printed p.911; H.5, pp.385–386,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Representation.BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

private theorem omega_commutator_residual (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) :
    ⁅omegaOneCenterAmbient (T : Subgroup G),P⁆ =
      ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 P).map P.subtype⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl (map_subtype_le _))
  rw [commutator_comm,commutator_comm _ ((pResidual 2 P).map P.subtype)]
  apply commutator_le.mpr
  intro p hp z hz
  obtain ⟨k,hk,t,ht,hkt⟩ := mem_sup_of_normal_left.mp
    ((pResidual_sup_sylow_eq_top (T.subtype hTP)) ▸ mem_top (⟨p,hp⟩ : P))
  have he : k.val*t.val = p := congrArg Subtype.val hkt
  have hzfix : t.val*z*t.val⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr
    (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t.val ht)
  have hec : ⁅p,z⁆ = ⁅k.val,z⁆ := by
    rw [←he,commutatorElement_def,commutatorElement_def,mul_inv_rev]
    calc
      k.val*t.val*z*(t.val⁻¹*k.val⁻¹)*z⁻¹ =
          k.val*(t.val*z*t.val⁻¹)*k.val⁻¹*z⁻¹ := by group
      _ = _ := by rw [hzfix]
  rw [hec]
  exact commutator_mem_commutator (mem_map_of_mem P.subtype hk) hz

/-- The actual point-core row of the original linear pair: the second fixed
line lies in the full H₀ socle and opposite residual commutator; the first
lies in neither. All three original quotient images use the same marking. -/
theorem original_pair_point_core_geometry
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv (BinaryLinearThree.U₂.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))))))) :
    let := he
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
    let Soc := (sSup {N : Subrepresentation ρ | IsAtom N}).toSubmodule
    Z ⊓ centralizer (B : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    ¬ Z ⊓ centralizer (A : Set G) ≤ ⁅Z,(pResidual 2 B).map B.subtype⁆ ∧
    binarySpace ((Z ⊓ centralizer (B : Set G)).subgroupOf U) ≤ Soc ∧
    ¬ binarySpace ((Z ⊓ centralizer (A : Set G)).subgroupOf U) ≤ Soc := by
  let := he
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let C := K.map X.subtype
  let Q := X.pCoreIn 2
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := q.surjective.comp (QuotientGroup.mk'_surjective _)
  change (A.subgroupOf C).map f = _ at hqA
  change (B.subgroupOf C).map f = _ at hqB
  change ((T : Subgroup G).subgroupOf C).map f = _ at hqT
  have hUX : U ≤ X := conjugateSpanBy_le_self (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hXU := le_normalizer_conjugateSpanBy Z X
  have hker := Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne hiA hiB
  have hUT : U ≤ (T : Subgroup G) := by
    have huq : U ≤ Q := by
      intro x hx
      exact mem_map_of_mem X.subtype (hker.1.le_pCore (show (⟨x,hUX hx⟩ : X) ∈ U.subgroupOf X from hx))
    exact huq.trans (hker.2.2.2.symm.le.trans inf_le_left)
  have hQT : Q ≤ (T : Subgroup G) := hker.2.2.2.symm.le.trans inf_le_left
  have hQU : Q ≤ centralizer (U : Set G) := hker.2.2.2.symm.le.trans inf_le_right
  have hgen : C ⊔ Q = X := (Amalgam.original_pair_linear_core_supplement
    h₀ D m h1332 hTA hTB eA eB hne hiA hiB K hK eK).2
  let : (Q.subgroupOf X).Normal := by
    change ((X.pCoreIn 2).subgroupOf X).Normal
    change (((pCore 2 X).map X.subtype).comap X.subtype).Normal
    rw [comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have reps (P : Subgroup G) (hPX : P ≤ X) (hQP : Q ≤ P) :=
    centralizing_supplement_representatives X C Q U P (map_subtype_le K) (pCoreIn_le 2 X)
      hgen hQU hPX hQP
  have hZ : U ⊓ centralizer (T : Set G) = Z := by
    apply le_antisymm
    · intro z hz
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hUT hz.1,
        elemPow_eq_one_of_isElementaryAbelian _ hz.1,hz.2⟩
    · exact le_inf (le_conjugateSpanBy Z X) (fun _ hz =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  have hfix (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) :
      U ⊓ centralizer (P : Set G) = Z ⊓ centralizer (P : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hZ ▸ ⟨hx.1,centralizer_le hTP hx.2⟩,hx.2⟩
    · exact inf_le_inf_right _ (le_conjugateSpanBy Z X)
  let S := modelSpace U C ((map_subtype_le K).trans hXU) f BinaryLinearThree.U₂ E
  have sZ : S Z = fixedSpace BinaryLinearThree.U₂ Matrix.PSL3Two.borelSL := by
    have hs := modelSpace_fixed U C ((map_subtype_le K).trans hXU) f BinaryLinearThree.U₂ E
      (T : Subgroup G) (reps (T : Subgroup G) (hTA.trans le_sup_left) hQT)
    change S (U ⊓ centralizer (T : Set G)) =
      fixedSpace BinaryLinearThree.U₂ (((T : Subgroup G).subgroupOf C).map f) at hs
    rw [hZ,hqT] at hs
    exact hs
  have sA : S (Z ⊓ centralizer (A : Set G)) =
      fixedSpace BinaryLinearThree.U₂ Matrix.PSL3Two.pointParabolicSL := by
    dsimp only [S]
    rw [←hfix A hTA,modelSpace_fixed U C ((map_subtype_le K).trans hXU) f BinaryLinearThree.U₂ E A (reps A le_sup_left (hQT.trans hTA)),hqA]
  have sB : S (Z ⊓ centralizer (B : Set G)) =
      fixedSpace BinaryLinearThree.U₂ Matrix.PSL3Two.lineParabolicSL := by
    dsimp only [S]
    rw [←hfix B hTB,modelSpace_fixed U C ((map_subtype_le K).trans hXU) f BinaryLinearThree.U₂ E B (reps B le_sup_right (hQT.trans hTB)),hqB]
  have sCA := modelSpace_commutator U C ((map_subtype_le K).trans hXU) f
    BinaryLinearThree.U₂ E Z A (le_conjugateSpanBy Z X) (le_sup_left.trans hXU)
    (reps A le_sup_left (hQT.trans hTA))
  have sCB := modelSpace_commutator U C ((map_subtype_le K).trans hXU) f
    BinaryLinearThree.U₂ E Z B (le_conjugateSpanBy Z X) (le_sup_right.trans hXU)
    (reps B le_sup_right (hQT.trans hTB))
  change S ⁅Z,A⁆ = subspaceCommutator BinaryLinearThree.U₂ (S Z) ((A.subgroupOf C).map f) at sCA
  change S ⁅Z,B⁆ = subspaceCommutator BinaryLinearThree.U₂ (S Z) ((B.subgroupOf C).map f) at sCB
  rw [sZ,hqA] at sCA
  rw [sZ,hqB] at sCB
  have hcU (P : Subgroup G) (hPX : P ≤ X) : ⁅Z,P⁆ ≤ U :=
    (commutator_mono (le_conjugateSpanBy Z X) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hPX.trans hXU))
  have transfer (P R : Subgroup G) (hPU : P ≤ U) (hRU : R ≤ U) : S P ≤ S R ↔ P ≤ R :=
    modelSpace_le_iff U C ((map_subtype_le K).trans hXU) f BinaryLinearThree.U₂ E hPU hRU
  have tests := BinaryLinearThree.FanoLocalStructure.point_core_flag_tests
  have h₁ : Z ⊓ centralizer (B : Set G) ≤ ⁅Z,A⁆ :=
    (transfer _ _ (inf_le_left.trans (le_conjugateSpanBy Z X)) (hcU A le_sup_left)).mp
      (by rw [sB,sCA]; exact tests.1)
  have h₂ : ¬ Z ⊓ centralizer (A : Set G) ≤ ⁅Z,B⁆ := by
    intro hle
    have hh := (transfer _ _ (inf_le_left.trans (le_conjugateSpanBy Z X)) (hcU B le_sup_right)).mpr hle
    rw [sA,sCB] at hh
    exact tests.2.1 hh
  rw [omega_commutator_residual A hTA] at h₁
  rw [omega_commutator_residual B hTB] at h₂
  refine ⟨h₁,h₂,?_,?_⟩
  all_goals
    let j := supplementSubrepresentationEquiv X U C hXU (map_subtype_le K) f hf BinaryLinearThree.U₂ E
      (reps X le_rfl (pCoreIn_le 2 X))
    have hj := supplement_socle X U C hXU (map_subtype_le K) f hf BinaryLinearThree.U₂ E
      (reps X le_rfl (pCoreIn_le 2 X))
  · rw [←hj]
    intro v hv
    obtain ⟨w,hw⟩ := E.surjective v
    change E w = v at hw
    refine ⟨w,?_,hw⟩
    apply tests.2.2.1
    rw [←sB]
    change (E w).toMul.val ∈ Z ⊓ centralizer (B : Set G)
    rw [hw]
    exact hv
  · intro hh
    apply tests.2.2.2
    intro w hw
    rw [←sA] at hw
    have hv := hh (show E w ∈ binarySpace ((Z ⊓ centralizer (A : Set G)).subgroupOf U) from hw)
    rw [←hj] at hv
    obtain ⟨v,hv,hev⟩ := hv
    exact (E.injective hev) ▸ hv
/-- Apply the point-core row to the literal Sylow-normalized second plane
and an escaping original centralizer. The weight test forces weight two,
and the original fixed line lies in both the full H₀ socle and [Z,O²(A)].
The whole-seed premise is supplied by either recognized component row. -/
theorem original_point_core_weight_and_socle
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv (BinaryLinearThree.U₂.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hAM : ¬ A ≤ normalizer (L : Set G)) :
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z (A ⊔ B)
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 2 ∧
    V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U) ≤
      (sSup {N : Subrepresentation ρ | IsAtom N}).toSubmodule := by
  let := he
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have geo := original_pair_point_core_geometry h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E
  have hz1 : z ≠ 1 := fun heq => hzL (congrArg Subtype.val heq ▸ one_mem _)
  have hfixA := m.central_four_fixed_of_escape h structural z hz1 hzT A hAz hAM
  rw [inf_eq_right.mpr hZV] at hfixA
  have hn : z.val ∉ ⁅Z,(pResidual 2 B).map B.subtype⁆ := by
    intro hz
    apply geo.2.1
    rw [hfixA]
    exact zpowers_le.mpr hz
  have hwtest := original_omega_residual_weight_iff D m hZV W hW hTW z hzT hz1
  rw [←hB] at hwtest
  have hw : m.weight z = 2 := by
    have hn4 : m.weight z ≠ 4 := fun hh => hn (hwtest.mpr hh)
    exact (m.nonfixed_weight z hzL).resolve_right hn4
  have hBM : B ≤ normalizer (L : Set G) := by rw [hB,hM]; exact inf_le_left
  have hF : V ⊓ centralizer (L : Set G) ≤ Z ⊓ centralizer (B : Set G) :=
    le_inf (Solvable.fixed_le_original_omegaCenter h structural D m)
      (le_centralizer_iff.mp (hBM.trans (normalizer_component_le_fixed_centralizer h structural D m)))
  refine ⟨hw,hF.trans geo.1,?_⟩
  exact fun v hv => geo.2.2.1 (hF hv)

/-- In the actual five-dimensional ordinary A₆ component row, the same
point-core H₀ model gives both source weights: z has weight two in V and
the original fixed generator has weight four in V_N. Outside-parabolic
uniqueness identifies the component weight test with the literal actor A. -/
theorem ordinary_point_core_both_weights
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv (BinaryLinearThree.U₂.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hAM : ¬ A ≤ normalizer (L : Set G))
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (N : Subgroup G)
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (eN : (N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6))
    (hfixedN : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆ :
      Subgroup G) ⊓ centralizer (N : Set G) ≠ ⊥)
    (hA : A ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U₀ := conjugateSpanBy Z (A ⊔ B)
    let U := ⁅conjugateSpanBy Z N,N⁆
    let ρ := elementaryRepresentation (p := 2)
      (U₀.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 2 ∧
    binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U₀) ≤
      (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule ∧
    ∃ DN : ChosenModule T N U, ∃ mN : CoreMarking DN, ∃ hd : m.constant.val ∈ U,
      mN.weight ⟨m.constant.val,hd⟩ = 4 := by
  have hs := original_point_core_weight_and_socle h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E h structural hM hZV W hW hTW hB
    z hzT hzL hAz hAM
  obtain ⟨DN,mN,hd,_,_,_,_,_,_,P,hP,hPH,_,_,_,htest,_⟩ :=
    ordinary_six_original_reciprocal_weight_detection h₀ h structural modules D m
      h1332 fixed hindex hM z hzT hzL hN hHN hNM hfN eN hfixedN
  obtain ⟨P₀,_,_,_,_,_,_,_,_,_,_,_,_,hunique⟩ :=
    ordinary_six_full_centralizer_parabolic h₀ h structural modules D m h1332 fixed
      hindex hM z hzT hzL hN hHN hNM hfN eN
  have hAP : A = P := (hunique A hA hAz).trans (hunique P hP hPH.le).symm
  refine ⟨hs.1,hs.2.2,DN,mN,hd,htest.mp ?_⟩
  rw [←hAP]
  exact hs.2.1

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- For either recognized natural component, the same point-core H₀ model
places the original fixed line in V_N. The independent large-distance input
remains explicit, as in the preceding component recognition. -/
theorem natural_point_core_weight_and_membership
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv (BinaryLinearThree.U₂.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hAM : ¬ A ≤ normalizer (L : Set G))
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (N : Subgroup G)
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (model : Nonempty ((N ⧸ pCore 2 N) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)))
    (hfixedN : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆ :
      Subgroup G) ⊓ centralizer (N : Set G) = ⊥)
    (hA : A ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U₀ := conjugateSpanBy Z (A ⊔ B)
    let U := ⁅conjugateSpanBy Z N,N⁆
    let ρ := elementaryRepresentation (p := 2)
      (U₀.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 2 ∧ V ⊓ centralizer (L : Set G) ≤ U ∧
    binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U₀) ≤
      (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule := by
  have hs := original_point_core_weight_and_socle h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E h structural hM hZV W hW hTW hB
    z hzT hzL hAz hAM
  have hv := (small_component_natural_residual_fixed_iff hl h₀ h structural modules D m
    h1332 fixed hindex hM z hzT hzL hN hHN hNM hfN model hfixedN A hA hAz).mp hs.2.1
  exact ⟨hs.1,hv,hs.2.2⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
