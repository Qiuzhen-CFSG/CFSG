module
public import Theory.Representation.G2BinaryPointElementaryAction
/-!
# The nontrivial elementary point-parabolic image moves exactly V₃

The already proved ABC containment reduces the image to three binary root
coordinates. Conjugation by rootE and rootC*rootD detects its second and
third coordinates; a nonidentity image therefore contains rootA. The Weyl
actor adds rootB. These two roots move three independent marked vectors,
whereas the invariant alternating pairing bounds every displacement by V₃.

This proves the literal equality [V,A₀]=[V,A₁]=V₃ used in
Aschbacher–Smith, Lemma 13.3.18, printed p.895, without a subgroup-classifier
premise or an assumed displacement lower bound.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup

private theorem conjugate_positive (t:Fin 6→F) (x:BinaryCore.elementaryCoordinates) :
    unipotentProduct t * BinaryCore.embedding x * (unipotentProduct t)⁻¹ =
      BinaryCore.embedding (BinaryCore.unipotentConjugate t x) := by
  change unipotentProduct t * unipotentProduct (BinaryCore.parameters x) *
    (unipotentProduct t)⁻¹=unipotentProduct _
  rw [unipotentProduct_inv,unipotentProduct_mul,unipotentProduct_mul,
    BinaryCore.unipotent_conjugate_parameters]

private theorem difference_E (x:BinaryCore.elementaryCoordinates) :
    (BinaryCore.embedding x)⁻¹*(rootE 1*BinaryCore.embedding x*(rootE 1)⁻¹)=rootA x.val.b := by
  have hE : rootE (1:F)=unipotentProduct ![0,0,0,0,1,0] := by simp [unipotentProduct]
  rw [hE,conjugate_positive,←map_inv,←map_mul]
  have hh : x.val⁻¹*BinaryCore.unipotentConjugate ![0,0,0,0,1,0] x=
      (⟨x.val.b,0,0,0,0⟩:BinaryCore.Coordinates) := by
    rcases x with ⟨⟨a,b,c,d,e⟩,hd,he⟩
    change d=0 at hd
    change e=0 at he
    subst d; subst e
    revert a b c
    decide +kernel
  rw [hh]
  simp [BinaryCore.embedding,BinaryCore.parameters,unipotentProduct]

private theorem difference_CD (x:BinaryCore.elementaryCoordinates) :
    (BinaryCore.embedding x)⁻¹*((rootC 1*rootD 1)*BinaryCore.embedding x*(rootC 1*rootD 1)⁻¹)=rootA x.val.c := by
  have hE : rootC (1:F)*rootD 1=unipotentProduct ![0,0,1,1,0,0] := by simp [unipotentProduct]
  rw [hE,conjugate_positive,←map_inv,←map_mul]
  have hh : x.val⁻¹*BinaryCore.unipotentConjugate ![0,0,1,1,0,0] x=
      (⟨x.val.c,0,0,0,0⟩:BinaryCore.Coordinates) := by
    rcases x with ⟨⟨a,b,c,d,e⟩,hd,he⟩
    change d=0 at hd
    change e=0 at he
    subst d; subst e
    revert a b c
    decide +kernel
  rw [hh]
  simp [BinaryCore.embedding,BinaryCore.parameters,unipotentProduct]

/-- Every nonzero normal elementary image contains the literal long-root four. -/
theorem natural_le_normalized_elementary (A:Subgroup (Model F))
    [IsElementaryAbelian 2 A] (hA:A≤unipotent)
    (hn:BinaryParabolicPair.derivedSecondAmbient≤normalizer (A:Set (Model F)))
    (hne:A≠⊥) : BinaryCore.natural≤A := by
  have hABC := elementary_normalized_point_le A hA hn
  obtain ⟨x,hx,hx1⟩ := (A.bot_or_exists_ne_one).resolve_left hne
  obtain ⟨t,ht,rfl⟩ := hABC hx
  let y : BinaryCore.elementaryCoordinates := ⟨t,ht⟩
  have hd (a:Model F) (ha:a∈BinaryParabolicPair.derivedSecondAmbient) :
      (BinaryCore.embedding y)⁻¹*(a*BinaryCore.embedding y*a⁻¹)∈A :=
    A.mul_mem (A.inv_mem hx) ((mem_normalizer_iff.mp (hn ha) _).mp hx)
  have hz : BinaryCore.z∈A := by
    by_cases hb : t.b=0
    · by_cases hc : t.c=0
      · have ha : t.a=1 := by
          have hnot : t.a≠0 := by
            intro ha
            apply hx1
            have ht1 : t=1 := by
              change t=⟨0,0,0,0,0⟩
              exact BinaryCore.Coordinates.ext ha hb hc ht.1 ht.2
            rw [ht1,map_one]
          exact ((by decide +kernel : ∀a:F,a=0∨a=1) _).resolve_left hnot
        have htZ : t=BinaryCore.involution := by
          change t=⟨1,0,0,0,0⟩
          exact BinaryCore.Coordinates.ext ha hb hc ht.1 ht.2
        simpa only [htZ,BinaryCore.embedding_involution,BinaryCore.z] using hx
      · have hc1 := ((by decide +kernel : ∀a:F,a=0∨a=1) _).resolve_left hc
        have hh:=hd (rootC 1*rootD 1) point_actor_membership.2.2
        rw [difference_CD] at hh
        simpa only [y,hc1,BinaryCore.z] using hh
    · have hb1 := ((by decide +kernel : ∀a:F,a=0∨a=1) _).resolve_left hb
      have hh:=hd (rootE 1) point_actor_membership.1
      rw [difference_E] at hh
      simpa only [y,hb1,BinaryCore.z] using hh
  have hw : (weylR:Model F)*BinaryCore.z*weylR⁻¹∈A :=
    (mem_normalizer_iff.mp (hn point_actor_membership.2.1) _).mp hz
  have hb : rootB (1:F)∈A := by
    have he : (weylR:Model F)*BinaryCore.z*weylR⁻¹=rootB 1 := by
      rw [BinaryCore.z,←BinaryCore.embedding_involution,
        BinaryCore.weyl_conjugate_elementary
          ⟨BinaryCore.involution,BinaryCore.involution_mem_elementary⟩]
      simp [BinaryCore.weylConjugate,BinaryCore.involution,BinaryCore.embedding,
        BinaryCore.parameters,unipotentProduct]
    rwa [he] at hw
  rintro _ ⟨t,ht,rfl⟩
  change BinaryCore.embedding t∈A
  have hprod : BinaryCore.embedding t=rootA t.a*rootB t.b := by
    simp [BinaryCore.embedding,BinaryCore.parameters,unipotentProduct,ht.1,ht.2.1,ht.2.2]
  rw [hprod]
  have hrootA : rootA t.a∈A := by
    rcases (by decide +kernel : ∀a:F,a=0∨a=1) t.a with ha|ha
    · rw [ha,rootA_zero]; exact A.one_mem
    · rw [ha]; exact hz
  have hrootB : rootB t.b∈A := by
    rcases (by decide +kernel : ∀a:F,a=0∨a=1) t.b with hb'|hb'
    · rw [hb',rootB_zero]; exact A.one_mem
    · rw [hb']; exact hb
  exact A.mul_mem hrootA hrootB
open Representation.BinaryOffender in
/-- A nontrivial elementary image normalized by the actual point parabolic
has exactly the marked seed as its full displacement space. -/
theorem normal_elementary_displacement_eq_seed (A:Subgroup (Model F))
    [IsElementaryAbelian 2 A] (hA:A≤unipotent)
    (hn:BinaryParabolicPair.derivedSecondAmbient≤normalizer (A:Set (Model F)))
    (hne:A≠⊥) :
    subspaceCommutator (Restricted.NaturalCoordinates.action F) ⊤ A=seed := by
  let M:=subspaceCommutator (Restricted.NaturalCoordinates.action F) ⊤ A
  have hAB:=natural_le_normalized_elementary A hA hn hne
  have ha:rootA (1:F)∈A := hAB BinaryCore.z_mem_natural
  have hb:rootB (1:F)∈A := hAB ⟨⟨0,1,0,0,0⟩,⟨rfl,rfl,rfl⟩,by
    simp [BinaryCore.embedding,BinaryCore.parameters,unipotentProduct]⟩
  have hm (g:Model F) (hg:g∈A) (v:W) :
      Restricted.NaturalCoordinates.action F g v-v∈M :=
    Submodule.subset_span ⟨g,hg,v,Submodule.mem_top,rfl⟩
  have h0:Pi.single (0:Fin 6) (1:F)∈M := by
    have hh:=hm (rootA 1) ha (Pi.single 4 1)
    have he:Restricted.NaturalCoordinates.action F (rootA 1) (Pi.single 4 1)-
        Pi.single 4 1=Pi.single 0 1 := by ext i;fin_cases i <;> simp
    rwa [he] at hh
  have h1:Pi.single (1:Fin 6) (1:F)∈M := by
    have hh:=hm (rootA 1) ha (Pi.single 5 1)
    have he:Restricted.NaturalCoordinates.action F (rootA 1) (Pi.single 5 1)-
        Pi.single 5 1=Pi.single 1 1 := by ext i;fin_cases i <;> simp
    rwa [he] at hh
  have h2:Pi.single (2:Fin 6) (1:F)∈M := by
    have hh:=hm (rootB 1) hb (Pi.single 5 1)
    have he:Restricted.NaturalCoordinates.action F (rootB 1) (Pi.single 5 1)-
        Pi.single 5 1=Pi.single 2 1 := by ext i;fin_cases i <;> simp
    rwa [he] at hh
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g,hg,w,_,rfl⟩
    exact displacement_mem_seed g (elementary_normalized_point_fixes_seed A hA hn g hg) w
  · intro v hv
    obtain ⟨v3,v4,v5⟩:=(mem_seed v).mp hv
    have he:v=v 0•Pi.single 0 1+v 1•Pi.single 1 1+v 2•Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp [v3,v4,v5]
    rw [he]
    exact M.add_mem (M.add_mem (M.smul_mem _ h0) (M.smul_mem _ h1)) (M.smul_mem _ h2)
end Atlas.G2.Natural.BinaryPointFlag
