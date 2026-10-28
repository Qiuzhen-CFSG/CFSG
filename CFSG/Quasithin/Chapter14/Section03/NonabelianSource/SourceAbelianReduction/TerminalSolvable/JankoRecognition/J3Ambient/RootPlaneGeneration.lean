module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.StrongEmbeddingExclusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneSplitting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.OutsideInvolutionFusion
public import BenderSuzuki.SE.SingleInvolutionClass
public import Theory.GroupTheory.CyclicHallNormalizerEscape

/-!
# Generation by the original centralizer and a returning root plane

The normalizer of an original elementary sixteen-plane fuses its nonidentity
points. The plane contains the distinguished involution, a noncentral core
involution, and an involution outside that core. The three local involution
classes therefore fuse inside the join with the original centralizer.
Its odd relative index puts every involution of the join into the centralizer.
A proper join would consequently be strongly embedded, contradicting the
actual returning-pair obstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem central_core_involution_eq
    (x : Janko23.localCore D.z) (hx : orderOf ((x : Janko23.involutionCentralizer D.z) : G) = 2)
    (hxZ : x ∈ center (Janko23.localCore D.z)) :
    ((x : Janko23.involutionCentralizer D.z) : G) = D.z := by
  let e : Janko23.localCore D.z ≃* Janko23.ambientCore D.z :=
    (Janko23.localCore D.z).equivMapOfInjective _
      (Janko23.involutionCentralizer D.z).subtype_injective
  have heZ : e x ∈ center (Janko23.ambientCore D.z) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨y,rfl⟩ := e.surjective q
    exact (e.map_mul y x).symm.trans
      ((congrArg e (mem_center_iff.mp hxZ y)).trans (e.map_mul x y))
  have hxline : ((x : Janko23.involutionCentralizer D.z) : G) ∈ zpowers D.z :=
    D.localType.core_center_image ▸ mem_map_of_mem (Janko23.ambientCore D.z).subtype heZ
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨((x : Janko23.involutionCentralizer D.z) : G),hxline⟩ : zpowers D.z))
    (y := (⟨D.z,mem_zpowers D.z⟩ : zpowers D.z))
    ((orderOf_coe _).symm.trans hx) ((orderOf_coe _).symm.trans D.localType.involution))

private theorem centralizer_involution_fusion_in_plane_join
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (y : G) (hyH : y ∈ Janko23.involutionCentralizer D.z) (hy : orderOf y = 2) :
    ∃ m ∈ Janko23.involutionCentralizer D.z ⊔ normalizer (A : Set G),
      m * D.z * m⁻¹ = y := by
  let H := Janko23.involutionCentralizer D.z
  let M := H ⊔ normalizer (A : Set G)
  have hEA := P.E_le_plane A hA hAR
  have hzA : D.z ∈ A := hEA P.z_mem_E
  have hz1 : D.z ≠ 1 := by
    intro he
    have hh := D.localType.involution
    simp [he] at hh
  have point (v : G) (hv : v ∈ A) (hv1 : v ≠ 1) :
      ∃ n ∈ M, n * D.z * n⁻¹ = v := by
    obtain ⟨n,hn,he⟩ := P.elementary_sixteen_normalizer_transitive hc A hA D.z v hzA hv hz1 hv1
    exact ⟨n,mem_sup_right hn,he⟩
  let yH : H := ⟨y,hyH⟩
  have hyH2 : orderOf yH = 2 := (orderOf_coe yH).symm.trans hy
  by_cases hyz : y = D.z
  · exact ⟨1,one_mem _,by simp [hyz]⟩
  by_cases hyQ : y ∈ Janko23.ambientCore D.z
  · have hyQ' : yH ∈ Janko23.localCore D.z := by
      rw [←Janko23.ambientCore_subgroupOf]
      exact hyQ
    let yQ : Janko23.localCore D.z := ⟨yH,hyQ'⟩
    have hyZ : yQ ∉ center (Janko23.localCore D.z) :=
      fun hh => hyz (central_core_involution_eq yQ hy hh)
    let uH : H := ⟨P.u,Janko23.ambientCore_le D.z P.mem_core⟩
    have huQ' : uH ∈ Janko23.localCore D.z := by
      rw [←Janko23.ambientCore_subgroupOf]
      exact P.mem_core
    let uQ : Janko23.localCore D.z := ⟨uH,huQ'⟩
    have huZ : uQ ∉ center (Janko23.localCore D.z) :=
      fun hh => P.ne (central_core_involution_eq uQ P.u_order hh)
    have huQ2 : orderOf uQ = 2 :=
      (orderOf_coe uQ).symm.trans ((orderOf_coe uH).symm.trans P.u_order)
    have hyQ2 : orderOf yQ = 2 := (orderOf_coe yQ).symm.trans hyH2
    obtain ⟨g,hg⟩ := isConj_iff.mp
      (D.localType.core_noncentral_involutions_isConj uQ yQ huQ2 huZ hyQ2 hyZ)
    have hu1 : P.u ≠ 1 := by
      intro he
      have hh := P.u_order
      simp [he] at hh
    obtain ⟨n,hn,he⟩ := point P.u (hEA P.u_mem_E) hu1
    refine ⟨(g : G)*n,mul_mem (mem_sup_left g.property) hn,?_⟩
    have hgy : (g : G)*P.u*(g : G)⁻¹ = y := congrArg Subtype.val hg
    calc
      ((g : G)*n)*D.z*((g : G)*n)⁻¹ = (g : G)*(n*D.z*n⁻¹)*(g : G)⁻¹ := by group
      _ = y := by rw [he,hgy]
  · have hnot : ¬ A ≤ Janko23.ambientCore D.z := by
      obtain ⟨e⟩ := Geometry.Coordinates.rootEquiv P
      rcases (P.elementary_sixteen_iff e A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
      · exact P.A₁_not_le_core e
      · exact P.A₂_not_le_core e
    obtain ⟨t,ht,htQ⟩ := SetLike.not_le_iff_exists.mp hnot
    have ht1 : t ≠ 1 := fun he => htQ (he ▸ one_mem _)
    have ht2 : orderOf t = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
    let tH : H := ⟨t,(P.R_le_double_centralizer (hAR ht)).1⟩
    obtain ⟨g,hg⟩ := isConj_iff.mp (D.localType.outside_involutions_isConj tH yH
      ((orderOf_coe tH).symm.trans ht2) hyH2 htQ hyQ)
    obtain ⟨n,hn,he⟩ := point t ht ht1
    refine ⟨(g : G)*n,mul_mem (mem_sup_left g.property) hn,?_⟩
    have hgy : (g : G)*t*(g : G)⁻¹ = y := congrArg Subtype.val hg
    calc
      ((g : G)*n)*D.z*((g : G)*n)⁻¹ = (g : G)*(n*D.z*n⁻¹)*(g : G)⁻¹ := by group
      _ = y := by rw [he,hgy]

/-- The original centralizer and any actual returning root plane normalizer
generate the whole ambient group. -/
theorem literal_centralizer_plane_normalizer_generate
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Janko23.involutionCentralizer D.z ⊔ normalizer (A : Set G) = ⊤ := by
  let H := Janko23.involutionCentralizer D.z
  let M := H ⊔ normalizer (A : Set G)
  have hHM : H ≤ M := le_sup_left
  have hindex : ¬2 ∣ (H.subgroupOf M).index := by
    have ho := D.localType.centralizer_odd_index hc
    exact fun hd => (Nat.not_even_iff_odd.mpr ho)
      (even_iff_two_dvd.mpr (dvd_trans hd (relIndex_dvd_index_of_le hHM)))
  have hzM : D.z ∈ M := hHM (mem_centralizer_singleton_iff.mpr rfl)
  by_contra hproper
  apply literal_not_strongly_embedded P M
  apply BenderSuzuki.isStronglyEmbedded_of_single_involution_class M hproper D.z
    D.localType.involution hzM hHM
  intro y hyM hy
  let yM : M := ⟨y,hyM⟩
  have hy2 : orderOf yM = 2 := (orderOf_coe yM).symm.trans hy
  have hp : IsPGroup 2 (zpowers yM) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hy2)
  obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index (H.subgroupOf M) (zpowers yM) hindex hp
  have hgyH : (g : G)*y*(g : G)⁻¹ ∈ H :=
    hg (mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers yM))
  have hgy2 : orderOf ((g : G)*y*(g : G)⁻¹) = 2 :=
    ((MulAut.conj (g : G)).orderOf_eq y).trans hy
  obtain ⟨n,hn,he⟩ := centralizer_involution_fusion_in_plane_join P hc A hA hAR
    ((g : G)*y*(g : G)⁻¹) hgyH hgy2
  refine ⟨(g : G)⁻¹*n,mul_mem (inv_mem g.property) hn,?_⟩
  calc
    ((g : G)⁻¹*n)*D.z*((g : G)⁻¹*n)⁻¹ =
        (g : G)⁻¹*(n*D.z*n⁻¹)*(g : G) := by group
    _ = y := by rw [he]; group

/-- Both literal root planes of the same returning pair give ambient generation. -/
theorem literal_returning_planes_generate
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    (Janko23.involutionCentralizer D.z ⊔ normalizer (P.A₁ eR : Set G) = ⊤) ∧
      (Janko23.involutionCentralizer D.z ⊔ normalizer (P.A₂ eR : Set G) = ⊤) :=
  ⟨literal_centralizer_plane_normalizer_generate P hc _ (P.A₁_card eR) (P.A₁_le_R eR),
    literal_centralizer_plane_normalizer_generate P hc _ (P.A₂_card eR) (P.A₂_le_R eR)⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
