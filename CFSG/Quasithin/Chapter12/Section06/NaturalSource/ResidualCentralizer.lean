module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidual
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.InvertedOdd
public import Theory.GroupTheory.RankTwoInvertedThree

/-!
# The remaining dihedral case in the original residual centralizer

F.9's exact centralizer preimage makes the original L₁-star centralize
V-star. A conjugator normalizing L₁ therefore gives a pair image that
centralizes L₁-star. Its original Sylow E₉ survives faithfully in H-star.
Three-rank two excludes inverted cubic elements in this centralizer, so
the earlier odd-order restriction reduces to order five.

Apply this to the square of the product of the same marked generators.
The D₆ and D₁₂ alternatives are impossible; only D₁₀ remains. The actual
conjugator, both marked generators and the quotient H -> H/O₂(H) are
retained throughout. This applies, in particular, to the normalizing
conjugators in C_H(L₁/O₂(L₁)). The orthogonal exclusion of D₁₀, the
relative-centralizer two-core bound, five-core exclusion and subsequent
source assembly still require proof; none is assumed or asserted here.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.831--832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original L₁-star centralizes V-star in the contrary-nonabelian branch. -/
theorem SourceHypothesis.original_point_residual_star_centralizes
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤
      centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H)) := by
  let E := D.fullSetup hZ T z
  have he := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
  rintro _ ⟨x,hx,rfl⟩
  change x ∈ (centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))).comap
    (QuotientGroup.mk' (pCore 2 H))
  rw [he]
  exact S.chosen.normalizes (((map_subtype_le _).trans inf_le_left : E.L₁ ≤ L) hx)

/-- A conjugate pair whose original conjugator normalizes L₁ centralizes
L₁-star through the literal H -> H/O₂(H) projection. -/
theorem SourceHypothesis.original_normalizing_pair_centralizes_residual
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (g : G) (hg : g ∈ H)
    (hgL : g ∈ normalizer ((D.fullSetup hZ T z).L₁ : Set G)) :
    Nonabelian.Setup.star H (V ⊔ V.map (MulAut.conj g).toMonoidHom) ≤
      centralizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (H ⧸ pCore 2 H)) := by
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let gH : H := ⟨g,hg⟩
  let C := centralizer (Nonabelian.Setup.star H E.L₁ : Set (H ⧸ pCore 2 H))
  have hbase : Nonabelian.Setup.star H V ≤ C := le_centralizer_iff.mpr
    (S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn)
  have hnH : gH ∈ normalizer (E.L₁.subgroupOf H : Set H) :=
    E.L₁.le_normalizer_comap H.subtype hgL
  have hnq : q gH ∈ normalizer (Nonabelian.Setup.star H E.L₁ : Set (H ⧸ pCore 2 H)) :=
    (E.L₁.subgroupOf H).le_normalizer_map q (mem_map_of_mem q hnH)
  have hnC : q gH ∈ normalizer (C : Set (H ⧸ pCore 2 H)) :=
    normalizer_le_normalizer_centralizer _ hnq
  have hVH : V ≤ H := S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx))
  have hVgH : V.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hg (hVH hv)) (H.inv_mem hg)
  rw [Nonabelian.Setup.star,subgroupOf_sup hVH hVgH,Subgroup.map_sup]
  refine sup_le hbase ?_
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨v,hv,he⟩ := hy
  let vH : H := ⟨v,hVH hv⟩
  have hvC : q vH ∈ C := hbase (mem_map_of_mem q hv)
  have hconj : q gH * q vH * (q gH)⁻¹ ∈ C := (mem_normalizer_iff.mp hnC _).mp hvC
  have hy : y = gH*vH*gH⁻¹ := Subtype.ext he.symm
  rw [hy,map_mul,map_mul,map_inv]
  exact hconj

/-- Inverted odd elements centralizing the original residual have order five.
The cubic possibility is excluded by the same original Sylow E₉ in H-star. -/
theorem SourceHypothesis.original_residual_centralizer_inverted_order_five
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (t : H ⧸ pCore 2 H) (ht : t ∈ Nonabelian.Setup.star H V)
    (x : H ⧸ pCore 2 H) (hx : x ≠ 1) (ho : Odd (orderOf x))
    (hi : t*x*t⁻¹=x⁻¹)
    (hc : x ∈ centralizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (H ⧸ pCore 2 H))) :
    orderOf x = 5 := by
  rcases S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH t ht x hx ho hi with h3 | h5
  · exfalso
    let E := D.fullSetup hZ T z
    let P : Sylow 3 E.L₁ := Sylow.nonempty.some
    let A := (P : Subgroup E.L₁).map E.L₁.subtype
    obtain ⟨hA,hcard,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH P
    let := hA
    have hAL : Nonabelian.Setup.star H A ≤ Nonabelian.Setup.star H E.L₁ :=
      map_mono (comap_mono (map_subtype_le _))
    have hcomm := S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn
    apply no_inverted_three_in_plane_centralizer (S.original_star_three_rank D hZ z hz hH)
      (Nonabelian.Setup.star H A) hcard t x _ _ hi h3
    · exact le_centralizer_iff.mpr (hAL.trans hcomm) ht
    · exact centralizer_le hAL hc
  · exact h5

/-- Among the original dihedral alternatives, a non-two pair with conjugator
normalizing L₁ can only have order ten. Both marked generators are retained. -/
theorem SourceHypothesis.original_normalizing_pair_dihedral_five
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hnH : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (g : G) (hg : g ∈ H)
    (hgL : g ∈ normalizer ((D.fullSetup hZ T z).L₁ : Set G))
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
    ∃ (hIH : I ≤ H) (v : V), v.val ∉ (D.fullSetup hZ T z).V₅ ∧
      Nonempty (Nonabelian.Setup.star H I ≃* DihedralGroup 5) ∧
      orderOf (QuotientGroup.mk' (pCore 2 H) (inclusion hIH ⟨v.val,mem_sup_left v.property⟩) *
        QuotientGroup.mk' (pCore 2 H) (inclusion hIH ⟨(MulAut.conj g) v.val,
          mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩))=5 := by
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  obtain ⟨hIH,v,m,hv,hm,he,ho⟩ :=
    S.original_non_two_pair_dihedral D hZ z hz hTV hTz hbound hns hH g hg hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let u : H := inclusion hIH ⟨v.val,mem_sup_left v.property⟩
  let w : H := inclusion hIH ⟨(MulAut.conj g) v.val,
    mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩
  let a := q u
  let b := q w
  have ha2 : a^2=1 := by
    rw [←map_pow,show u^2=1 from Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val v.property),map_one]
  have hb2 : b^2=1 := by
    have hw : w^2=1 := by
      apply Subtype.ext
      change ((MulAut.conj g) v.val)^2=1
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian v.val v.property,map_one]
    rw [←map_pow,hw,map_one]
  have hinv : a*(a*b)*a⁻¹=(a*b)⁻¹ := by
    have haa : a*a=1 := by simpa only [pow_two] using ha2
    have hbb : b*b=1 := by simpa only [pow_two] using hb2
    have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right haa
    have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_right hbb
    rw [_root_.mul_inv_rev,hai,hbi]
    simp only [←mul_assoc,haa,one_mul]
  have hi2 : a*(a*b)^2*a⁻¹=((a*b)^2)⁻¹ := by
    calc
      _ = (a*(a*b)*a⁻¹)^2 := (conj_pow (i := 2) (a := a) (b := a*b)).symm
      _ = _ := by rw [hinv,inv_pow]
  have hc := S.original_normalizing_pair_centralizes_residual D hZ z hz hTV hTz hbound hH hnH g hg hgL
  have hex (horder : orderOf ((a*b)^2)=3) : False := by
    have hnzero : (a*b)^2 ≠ 1 := fun he => by rw [he,orderOf_one] at horder;omega
    have h5 := S.original_residual_centralizer_inverted_order_five D hZ z hz hTV hTz hbound hns
      hH hnH a (mem_map_of_mem q v.property) ((a*b)^2) hnzero
      (by rw [horder];decide) hi2
      (hc ((Nonabelian.Setup.star H I).pow_mem
        ((Nonabelian.Setup.star H I).mul_mem
          (mem_map_of_mem q (mem_sup_left v.property))
          (mem_map_of_mem q (mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)))) 2))
    omega
  have hm5 : m=5 := by
    rcases hm with h3|h5|h6
    · exact (hex (by rw [orderOf_pow,ho,h3];norm_num)).elim
    · exact h5
    · exact (hex (by rw [orderOf_pow,ho,h6];norm_num)).elim
  exact ⟨hIH,v,hv,hm5 ▸ he,ho.trans hm5⟩
end CFSG.Quasithin.Chapter12.Section06
