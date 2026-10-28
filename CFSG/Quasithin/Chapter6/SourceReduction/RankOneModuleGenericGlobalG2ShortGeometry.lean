module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortOrbits
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2LocalFusion
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong.Coordinates
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Nonfusion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# The plane and fixed-coset geometry of the G₂ short-root centralizer

In the original common Sylow, a long involution centralizing the pinned C-root
lies either in the A–B plane or in the C-centralizer orbit of the E-root.
Coordinates give these two possibilities. The actual compatible parabolic maps
reflect long-root fusion, and commuting-pair exchange separates the two orbits
in the full ambient centralizer. Thus the orbit containing the pinned A-root
recovers exactly the nonidentity elements of the A–B plane inside C_S(v).

A full common stabilizer normalizes C_K(v)=C_S(v) and preserves this orbit,
so it normalizes the plane. Once the source uniqueness argument places that
normalizer in N_G(L), Sylow conjugacy inside N_G(L) intersect C_G(v) proves
that the pinned A-root fixes a unique coset. The only extra premise for this
last step is S=T, consumed by the existing short-root extremality theorem.
No exhaustive orbit-coverage premise is required in this proof.

The separate coordinate and pointwise transport lemmas avoid the large
combined dependent transport from the earlier coverage draft. Internal imports
reuse proved helpers from this same source family without changing their
public boundaries. The source application is in G2ShortFixed.
Source: Aschbacher–Smith F.4.42, printed p.295, and 5.3.3, p.659
(`refs/quasithin.pdf`). Root coordinates reuse the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry
variable {F : Type} [Field F] [Finite F] [CharP F 2]
private theorem outside_orbit (a e : F) (he : e ≠ 0) :
    ∃ g ∈ centralizer ({rootC (1:F)} : Set (Model F)),
      MulAut.conj g (rootE 1) = rootA a * rootE e := by
  obtain ⟨u,hu⟩ := isSquare_of_charTwo' e
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu; exact he hu
  let m := Units.mk0 u hu0
  have hm : torus 1 m ∈ centralizer ({rootC (1:F)} : Set (Model F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    simpa using torus_rootC (1:Fˣ) m (1:F)
  have hb : rootB (a/e) ∈ centralizer ({rootC (1:F)} : Set (Model F)) :=
    residualBlock_le_centralizer_rootC 1 (mem_sup_left (rootB_mem_longRootLocal _))
  refine ⟨rootB (a/e) * torus 1 m,mul_mem hb hm,?_⟩
  rw [map_mul,MulAut.mul_apply]
  have hE : MulAut.conj (torus 1 m) (rootE (1:F)) = rootE e := by
    simpa [m,←hu,pow_two] using torus_rootE (1:Fˣ) m (1:F)
  rw [hE]
  have hB : MulAut.conj (rootB (a/e)) (rootE e) = rootA ((a/e)*e) * rootE e := by
    change rootB (a/e) * rootE e * (rootB (a/e))⁻¹ = _
    have hb' : rootB (a/e) = unipotentProduct ![0,a/e,0,0,0,0] := by simp [unipotentProduct]
    have he' : rootE e = unipotentProduct ![0,0,0,0,e,0] := by simp [unipotentProduct]
    rw [hb',he',unipotentProduct_inv,unipotentProduct_mul,unipotentProduct_mul]
    have ht : unipotentProductParameters
        (unipotentProductParameters ![0,a/e,0,0,0,0] ![0,0,0,0,e,0])
        (unipotentInverseParameters ![0,a/e,0,0,0,0]) = ![(a/e)*e,0,0,0,e,0] := by
      ext i
      fin_cases i <;> simp [unipotentProductParameters,unipotentInverseParameters,CharTwo.neg_eq,CharTwo.add_self_eq_zero]
    rw [ht]
    simp [unipotentProduct]
  rw [hB,div_mul_cancel₀ _ he]

/-- The two planes containing the long involutions of the short Sylow centralizer. -/
theorem long_plane_or_outside (x : Model F) (hx : x ∈ unipotent)
    (hc : Commute x (rootC 1)) (hl : ShortRootProducts.IsLongRootElement x) :
    x ∈ longRootLocal ∨ ∃ g ∈ centralizer ({rootC (1:F)} : Set (Model F)),
      MulAut.conj g (rootE 1) = x := by
  obtain ⟨t,rfl⟩ := (unipotent_eq_range (K := F)).le hx
  have hc' := G2Nonfusion.centralizer_coordinates t hc
  have hlong := EvenInvolutionGeometry.PureLong.unipotent_long_coordinates t hl
  have hc0 : t 2 = 0 := by
    have hh : (t 2)^2=0 := by simpa [hc'.1] using hlong.2.2.1
    exact (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp hh
  have hbe : t 1 * t 4=0 := by simpa [hc'.1] using hlong.2.2.2
  have hshape : unipotentProduct t = rootA (t 0) * rootB (t 1) * rootE (t 4) := by
    simp [unipotentProduct,hc'.1,hc'.2,hc0]
  by_cases he : t 4=0
  · apply Or.inl
    refine ⟨Multiplicative.ofAdd (t 0,t 1),?_⟩
    simpa [longRootHom,he] using hshape.symm
  · apply Or.inr
    have hb : t 1=0 := (mul_eq_zero.mp hbe).resolve_right he
    obtain ⟨g,hg,hge⟩ := outside_orbit (t 0) (t 4) he
    exact ⟨g,hg,by simpa [hshape,hb] using hge⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

private theorem long_order : orderOf (G2CompletionFusion.long (1:F))=2 :=
  (Subgroup.orderOf_coe _).symm.trans (ShortRootProducts.rootA_twoCentral (F := F) one_ne_zero).1

private theorem long_model_of_image
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩)
    (hn : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)))
    (a : parabolic₁ (F := F))
    (hx : IsConj (f (G2CompletionFusion.long 1)) (f a)) :
    ShortRootProducts.IsLongRootElement a.val := by
  have ha2 : orderOf a=2 := by
    rw [←orderOf_injective f hf]
    obtain ⟨g,hg⟩ := isConj_iff.mp hx
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq _).trans ((orderOf_injective f hf _).trans long_order)
  have hh := ((G2LocalFusion.compatible_parabolic_fusion f l ha hn).1 _ _ long_order ha2).mp hx
  obtain ⟨g,hg⟩ := isConj_iff.mp hh
  exact ⟨1,one_ne_zero,g,hg.symm⟩

omit [Finite F] in
private theorem mapped_outside_orbit
    (l : parabolic₂ (F := F) →* G)
    (a : parabolic₂ (F := F))
    (x : centralizer ({l G2ShortAction.short} : Set G))
    (ha : l a=x.val)
    (g : Model F) (hg : g ∈ centralizer ({rootC (1:F)} : Set (Model F)))
    (hge : MulAut.conj g (rootE 1)=a.val) :
    IsConj (G2ShortOrbits.outsideMark l) x := by
  let gP : parabolic₂ (F := F) := ⟨g,centralizer_rootC_le_parabolic 1 one_ne_zero hg⟩
  have hgC : l gP ∈ centralizer ({l G2ShortAction.short} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg l (Subtype.ext (mem_centralizer_singleton_iff.mp hg))
  apply isConj_iff.mpr
  refine ⟨⟨l gP,hgC⟩,Subtype.ext ?_⟩
  change l gP*l G2ShortOrbits.outside*(l gP)⁻¹=x.val
  rw [←map_inv,←map_mul,←map_mul,←ha]
  exact congrArg l (Subtype.ext hge)

/-- Inside the original common Sylow, the full-centralizer orbit of A
is precisely the nonidentity part of the A–B plane. -/
theorem plane_of_sylow_conjugate
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩)
    (hn : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)))
    (hsep : ¬ IsConj (G2ShortAction.longMark l) (G2ShortOrbits.outsideMark l))
    (x : centralizer ({l G2ShortAction.short} : Set G))
    (hS : x.val ∈ (unipotent.subgroupOf parabolic₁).map f)
    (hx : IsConj (G2ShortAction.longMark l) x) :
    x.val ∈ G2ShortAction.plane l := by
  obtain ⟨a,haU,hea⟩ := hS
  have hv : f (G2CompletionFusion.short 1)=l G2ShortAction.short := ha _ _ _
  have hz : f (G2CompletionFusion.long 1)=l G2ShortAction.long := ha _ _ _
  have hc : Commute a.val (rootC (1:F)) := by
    have hh : a * G2CompletionFusion.short (1:F)=G2CompletionFusion.short 1 * a := by
      apply hf
      rw [map_mul,map_mul,hea,hv]
      exact mem_centralizer_singleton_iff.mp x.property
    exact congrArg Subtype.val hh
  have hlong : ShortRootProducts.IsLongRootElement a.val := by
    apply long_model_of_image f hf l ha hn a
    rw [hea,hz]
    exact (centralizer ({l G2ShortAction.short} : Set G)).subtype.map_isConj hx
  let b : parabolic₂ (F := F) :=
    ⟨a.val,unipotent_le_local₂.trans local₂_le_parabolic₂ haU⟩
  have heb : l b=x.val := (ha _ a.property b.property).symm.trans hea
  rcases long_plane_or_outside a.val haU hc hlong with hplane | ⟨g,hg,hge⟩
  · exact ⟨b,hplane,heb⟩
  · exact (hsep (hx.trans (mapped_outside_orbit l b x heb g hg hge).symm)).elim

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry
variable {G : Type*} [Group G]

private theorem common_normalizes_plane (C K S V : Subgroup G) (z : C)
    (hCK : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKC : K ⊓ C=S ⊓ C) (hVS : V ≤ S) (hVC : V ≤ C)
    (horbit : ∀ x : C, x.val ∈ V → x ≠ 1 → IsConj z x)
    (hplane : ∀ x : C, x.val ∈ S → IsConj z x → x.val ∈ V) :
    C ⊓ centralizer ({z.val} : Set G) ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  by_cases hx1 : x=1
  · simp [hx1]
  let y : C := ⟨x,hVC hx⟩
  let a : C := ⟨g,hg.1⟩
  have hy1 : y ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hxK : x ∈ K := (hKC.ge ⟨hVS hx,hVC hx⟩).1
  have hgxK : g*x*g⁻¹ ∈ K := (mem_normalizer_iff.mp (hCK hg.2) x).mp hxK
  have hgyS : (a*y*a⁻¹).val ∈ S := (hKC.le ⟨hgxK,(a*y*a⁻¹).property⟩).1
  exact hplane (a*y*a⁻¹) hgyS ((horbit y hx hy1).trans (isConj_iff.mpr ⟨a,rfl⟩))

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem plane_le_sylow_image
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩) :
    G2ShortAction.plane l ≤ (unipotent.subgroupOf parabolic₁).map f := by
  rintro _ ⟨a,haP,rfl⟩
  have hU := longRootLocal_le_unipotent haP
  exact ⟨⟨a.val,unipotent_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel) hU⟩,
    hU,ha _ _ _⟩

/-- Pair stabilizers preserve the actual root plane, using only the original
factor centralizer and the two separated full-centralizer orbits. -/
theorem common_stabilizer_le_plane_normalizer
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩)
    (hn : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)))
    (hsep : ¬ IsConj (G2ShortAction.longMark l) (G2ShortOrbits.outsideMark l))
    (K : Subgroup G)
    (hCK : centralizer ({l G2ShortAction.long} : Set G) ≤ normalizer (K : Set G))
    (hKC : K ⊓ centralizer ({l G2ShortAction.short} : Set G)=
      (unipotent.subgroupOf parabolic₁).map f ⊓ centralizer ({l G2ShortAction.short} : Set G)) :
    centralizer ({l G2ShortAction.short} : Set G) ⊓
      centralizer ({l G2ShortAction.long} : Set G) ≤
        normalizer (G2ShortAction.plane l : Set G) := by
  apply common_normalizes_plane _ K _ _ (G2ShortAction.longMark l) hCK hKC
    (plane_le_sylow_image f l ha) (G2ShortAction.plane_centralizes l)
  · exact G2ShortAction.plane_orbit l
  · exact plane_of_sylow_conjugate f hf l ha hn hsep

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry



namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

omit [Finite F] in
private theorem plane_local_conjugator (l : parabolic₂ (F := F) →* G)
    (x : centralizer ({l G2ShortAction.short} : Set G))
    (hx : x.val ∈ G2ShortAction.plane l) (hx1 : x ≠ 1) :
    ∃ g ∈ l.range, g ∈ centralizer ({l G2ShortAction.short} : Set G) ∧
      g * l G2ShortAction.long * g⁻¹=x.val := by
  obtain ⟨a,ha,hea⟩ := hx
  have hac : a ∈ centralizer ({G2ShortAction.short} : Set (parabolic₂ (F := F))) := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (residualBlock_le_centralizer_rootC 1 (mem_sup_left ha))
  let y : centralizer ({G2ShortAction.short} : Set (parabolic₂ (F := F))) := ⟨a,hac⟩
  have hy1 : y ≠ 1 := by
    intro hy
    apply hx1
    apply Subtype.ext
    rw [←hea,show a=1 from congrArg Subtype.val hy,map_one]
    rfl
  have hyP : y.val ∈ G2ShortAction.plane (MonoidHom.id (parabolic₂ (F := F))) :=
    mem_map_of_mem _ ha
  obtain ⟨g,hg⟩ := isConj_iff.mp (G2ShortAction.plane_orbit
    (MonoidHom.id (parabolic₂ (F := F))) y hyP hy1)
  refine ⟨l g.val,⟨_,rfl⟩,mem_centralizer_singleton_iff.mpr ?_,?_⟩
  · simpa only [map_mul,MonoidHom.id_apply] using congrArg l (mem_centralizer_singleton_iff.mp g.property)
  · rw [←map_inv,←map_mul,←map_mul,←hea]
    exact congrArg l (congrArg Subtype.val hg)

private theorem unique_of_sylow_plane {C : Type*} [Group C] [Finite C]
    (X V : Subgroup C) (P : Sylow 2 C) (hPX : (P : Subgroup C) ≤ X)
    (z : C) (hzV : z ∈ V) (hz2 : orderOf z=2) (hVX : V ≤ X)
    (hcentral : centralizer ({z} : Set C) ≤ X)
    (hplane : ∀ y : C, y ∈ (P : Subgroup C) → IsConj z y → y ∈ V)
    (horbit : ∀ y ∈ V, y ≠ 1 → ∃ x ∈ X, x*z*x⁻¹=y) :
    ∃! q : C ⧸ X, z • q=q := by
  apply UniqueFixedCoset.unique_of_transporter (hVX hzV)
  intro g hg
  let y : X := ⟨g*z*g⁻¹,hg⟩
  let R := P.subtype hPX
  have hy2 : orderOf y=2 := by
    rw [←Subgroup.orderOf_coe]
    exact ((MulAut.conj g).orderOf_eq z).trans hz2
  obtain ⟨a,ha⟩ := R.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hy2)
  obtain ⟨b,hb⟩ := isConj_iff.mp ha
  have hab : b.val*g*z*(b.val*g)⁻¹=a.val.val := by
    have hh := congrArg Subtype.val hb
    change b.val*(g*z*g⁻¹)*b.val⁻¹=a.val.val at hh
    simpa only [mul_inv_rev,mul_assoc] using hh
  have haV := hplane a.val.val a.property (isConj_iff.mpr ⟨b.val*g,hab⟩)
  have ha1 : a.val.val ≠ 1 := by
    intro h1
    have hh := ((MulAut.conj (b.val*g)).orderOf_eq z).trans hz2
    change orderOf (b.val*g*z*(b.val*g)⁻¹)=2 at hh
    rw [hab,h1,orderOf_one] at hh
    contradiction
  obtain ⟨c,hc,hcz⟩ := horbit _ haV ha1
  have hk : c⁻¹*(b.val*g) ∈ centralizer ({z} : Set C) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      _ = c⁻¹*(b.val*g*z*(b.val*g)⁻¹)*c := by group
      _ = z := by rw [hab,←hcz]; group
  have hm := X.mul_mem hc (hcentral hk)
  have hm' : b.val*g ∈ X := by simpa only [mul_inv_cancel_left] using hm
  simpa only [inv_mul_cancel_left] using X.mul_mem (X.inv_mem b.property) hm'

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] [Finite G]

/-- The pinned long root fixes a unique coset, using the proved pair
stabilizer bound and Sylow conjugacy within the proposed point stabilizer. -/
theorem long_unique_fixed
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩)
    (hn : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)))
    (hsep : ¬ IsConj (G2ShortAction.longMark l) (G2ShortOrbits.outsideMark l))
    (N : Subgroup G) (hN : l.range ≤ N)
    (hcommon : centralizer ({l G2ShortAction.short} : Set G) ⊓
      centralizer ({l G2ShortAction.long} : Set G) ≤ N)
    (T : Sylow 2 G) (hS : (unipotent.subgroupOf parabolic₁).map f=(T : Subgroup G)) :
    ∃! q : centralizer ({l G2ShortAction.short} : Set G) ⧸
      N.subgroupOf (centralizer ({l G2ShortAction.short} : Set G)),
      G2ShortAction.longMark l • q=q := by
  let C := centralizer ({l G2ShortAction.short} : Set G)
  let X := N.subgroupOf C
  let V := (G2ShortAction.plane l).subgroupOf C
  let z := G2ShortAction.longMark l
  have hv : f (G2CompletionFusion.short 1)=l G2ShortAction.short := ha _ _ _
  have hs : ∃ P : Sylow 2 C, (P : Subgroup C)=(T : Subgroup G).subgroupOf C := by
    have hh := (G2ShortSylow.compatible_short_sylow f hf l ha T hS hn).2
    rw [hv] at hh
    exact hh
  obtain ⟨P,hP⟩ := hs
  have hPX : (P : Subgroup C) ≤ X := by
    rw [hP]
    intro x hx
    change x.val ∈ N
    rw [←hS] at hx
    obtain ⟨a,haU,hea⟩ := hx
    let b : parabolic₂ (F := F) := ⟨a.val,unipotent_le_local₂.trans local₂_le_parabolic₂ haU⟩
    exact hN ⟨b,(ha _ a.property b.property).symm.trans hea⟩
  have hz2 : orderOf z=2 := by
    rw [←Subgroup.orderOf_coe]
    change orderOf (l G2ShortAction.long)=2
    have hz : l G2ShortAction.long=f (G2CompletionFusion.long 1) := (ha _ _ _).symm
    rw [hz,orderOf_injective f hf]
    exact long_order
  apply unique_of_sylow_plane X V P hPX z
    (mem_map_of_mem l (rootA_mem_longRootLocal 1)) hz2
    (fun _ hx => hN (map_le_range l _ hx))
  · intro x hx
    apply hcommon
    refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
  · intro y hy hyz
    have hyT : y.val ∈ (T : Subgroup G) := by
      rw [hP] at hy
      exact hy
    exact plane_of_sylow_conjugate f hf l ha hn hsep y (hS.symm ▸ hyT) hyz
  · intro y hy hy1
    obtain ⟨g,hgr,hgc,hge⟩ := plane_local_conjugator l y hy hy1
    exact ⟨⟨g,hgc⟩,hN hgr,Subtype.ext hge⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortGeometry
