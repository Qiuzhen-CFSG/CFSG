module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointOffender
public import Theory.SpecificGroups.Alternating.FiveSquareCoreImage.Generation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorFiveAmbient
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation

/-!
# The Sylow offender in the original tensor point-core argument

In the contrary branch of 8.3.12, the image of V modulo the whole point
two-core has order sixteen. The faithful action on the normal A₅ square
supplies a nontrivial inner element of that image. Irreducibility of the
original upper tensor layer then puts the whole image inside the square.
Its order is the square's full two-part, so it is a Sylow subgroup there.
Two conjugates generate that image, with a conjugator in the original K_z.
The Source application supplies the square marking and the full action
kernel from the original ambient point-centralizer argument.

Source: Aschbacher--Smith 8.3.12, printed p.726, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 Chapter8.Section03 Chapter1 BinaryTensorThree
variable {G : Type*} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The source's swapped prime-five quotient is marked by the actual alternating square. -/
theorem quiet_tensor_swapped_five_square
    {X P H I : Subgroup G}
    (hs : Chapter1.XiEmbedding.SwappedSylowInput KnownSimple.IsKnownSimple 3
      (T : Subgroup G) X P H I)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 5) :
    Nonempty ((componentOrbit I (T : Subgroup G) ⧸
      pCore 2 (componentOrbit I (T : Subgroup G))) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  obtain ⟨c⟩ := swapped_product hs
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f : XiQuotient I ≃* alternatingGroup (Fin 5) :=
    a.trans ((GorensteinWalter.psl2RingEquiv eF).symm.trans
      GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm)
  exact ⟨c.trans (f.prodCongr f)⟩

variable (q : localJoin T L →* PointParabolic.Actor) (hq : Function.Surjective q)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
  (hz1 : z ≠ 1)

include hq hb hbz hzT hz1 in
/-- The order-sixteen original offender lies in the actual normal square,
modulo the full point two-core. -/
theorem quiet_tensor_point_module_le_component_core
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (e : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      (d.Kz ⧸ pCore 2 d.Kz) ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (hker : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      IsPGroup 2 ((pCoreNormalizerAction 2 d.Kz).comp
        (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))).ker) :
    D.fullModule ≤ CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ ⊔
      (centralizer ({z} : Set G)).pCoreIn 2 := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let Q := d.Gz.pCoreIn 2
  let A := D.fullModule ⊓ (d.Kz ⊔ Q)
  have hs := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  have h5Q : quietTensorFive D b ≤ Q := (le_conjugateSpanBy _ _).trans hs.U_le_core
  have h5A : quietTensorFive D b ≤ A := le_inf (quietTensorFive_le D b)
    (h5Q.trans le_sup_right)
  have hQN : d.Gz ≤ normalizer (Q : Set G) := by
    simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 d.Gz).le_normalizer_map d.Gz.subtype
  have hKN : d.Gz ≤ normalizer ((d.Kz ⊔ Q : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_conjugateSpanBy d.X d.Gz) hQN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXH : d.XT ≤ d.Gz := sup_le (d.X_le.trans inf_le_right) hzT
  have hVN : d.XT ≤ normalizer (D.fullModule : Set G) := by
    rw [quiet_XT_eq_point_centralizer (T := T) (L := L) hzT]
    exact inf_le_left.trans
      ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
        D.maximalLocal_normalizes_fullModule)
  have hAN : d.XT ≤ normalizer (A : Set G) :=
    (le_inf hVN (hXH.trans hKN)).trans inf_normalizer_le_normalizer_inf
  rcases quiet_tensor_point_upper_irreducible D q hq b hb hzV hbz hzT A h5A inf_le_left hAN with
    heq | heq
  · obtain ⟨v,hv,hvK,hvQ⟩ :=
      Theory.SpecificGroups.Alternating.FiveSquareCoreImage.exists_nontrivial_component_image
        d.Gz d.Kz D.fullModule d.Kz_le_Gz (le_normalizer_conjugateSpanBy d.X d.Gz)
        ((D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT)
        e hker (by
          have hc := quiet_tensor_point_core_image_card D q hq b hb hzV hbz hzT hz1 hcore
          change Nat.card ((D.fullModule.subgroupOf d.Gz).map (QuotientGroup.mk' (pCore 2 d.Gz))) = 16 at hc
          rw [hc]; decide)
    exact (hvQ (h5Q (heq ▸ (show v ∈ A from ⟨hv,hvK⟩)))).elim
  · exact heq ▸ (show A ≤ d.Kz ⊔ Q from inf_le_right)

include hq hb hbz hzT hz1 in
/-- The image of V is Sylow in the literal image of K_z in C_G(z)/O₂(C_G(z)). -/
theorem quiet_tensor_point_image_sylow
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (e : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      (d.Kz ⧸ pCore 2 d.Kz) ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (hker : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      IsPGroup 2 ((pCoreNormalizerAction 2 d.Kz).comp
        (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))).ker) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let π := QuotientGroup.mk' (pCore 2 d.Gz)
    IsSylowIn 2 ((D.fullModule.subgroupOf d.Gz).map π) ((d.Kz.subgroupOf d.Gz).map π) := by
  exact Theory.SpecificGroups.Alternating.FiveSquareCoreImage.exists_sylow_core_image
    _ _ _ (CentralizerSetup.Kz_le_Gz _) (le_normalizer_conjugateSpanBy _ _) e
    (quiet_tensor_point_module_le_component_core D q hq b hb hzV hbz hzT hz1 hcore e hker)
    (quiet_tensor_point_core_image_card D q hq b hb hzV hbz hzT hz1 hcore)

include hq hb hbz hzT hz1 in
/-- The original component image is generated by V's image and an actual K_z-conjugate. -/
theorem quiet_tensor_point_two_conjugates
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (e : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      (d.Kz ⧸ pCore 2 d.Kz) ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (hker : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      IsPGroup 2 ((pCoreNormalizerAction 2 d.Kz).comp
        (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))).ker) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let π := QuotientGroup.mk' (pCore 2 d.Gz)
    let A := (D.fullModule.subgroupOf d.Gz).map π
    ∃ k : d.Kz, A ⊔ A.map (MulAut.conj (π (inclusion d.Kz_le_Gz k))).toMonoidHom =
      (d.Kz.subgroupOf d.Gz).map π := by
  exact Theory.SpecificGroups.Alternating.FiveSquareCoreImage.exists_core_image_generating_conjugate
    _ _ _ (CentralizerSetup.Kz_le_Gz _) (le_normalizer_conjugateSpanBy _ _) e
    (quiet_tensor_point_module_le_component_core D q hq b hb hzV hbz hzT hz1 hcore e hker)
    (quiet_tensor_point_core_image_card D q hq b hb hzV hbz hzT hz1 hcore)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
