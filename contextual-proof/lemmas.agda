{-# OPTIONS --allow-unsolved-metas #-}
module lemmas where

open import rules public
open import logical-relations public

L1′ : ∀ (Σ₁ Σ₂ : Sens) → (Σ₁ +[qty] Σ₂) ≡ (Σ₂ +[qty] Σ₁)
L1′ Σ₁ Σ₂ = commu[+]< Σ₁ , Σ₂ >

L1 : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → (Σ₁ ⨰ Σ₂) ≡ (Σ₂ ⨰ Σ₁)
L1 [] [] = ↯
L1 (x ∷ a) (x₁ ∷ b) rewrite commu[×]< x , x₁ > | L1 a b = ↯

L0-1 : ∀ {N} (Σ : Σ[ N ]) → zero ⨰ Σ ≡< qty ℕ > ⟨ 0 ⟩
L0-1 e = lzero[⨰]< e >

L0-3 : ∀ (s : Sens) → ⟨ 0 ⟩ +[qty] s ≡< qty ℕ > s
L0-3 ⟨ x ⟩ = ↯
L0-3 `∞ = ↯

L0-3′ : ∀ (s : Sens) → s ≡< qty ℕ > ⟨ 0 ⟩ +[qty] s
L0-3′ s = ◇ (lunit[+][qty]< s >)

L0-4 : ∀ (s : Sens) → (s +[qty] ⟨ 0 ⟩) ≡< qty ℕ > s
L0-4 s = runit[+][qty]< s >

L0-4′ : ∀ (s : Sens) → s ≡< qty ℕ > s +[qty] ⟨ 0 ⟩
L0-4′ s = ◇ (runit[+][qty]< s >)

L0-5 : ∀ {N} (Σ₁ : Σ[ N ]) (Σ₂ : Σ[ ꜱ N ]) → ((⟨ 0 ⟩ ∷ Σ₁ ⨰ Σ₂) +[qty] ⟨ 0 ⟩) ≡ (⟨ 0 ⟩ ∷ Σ₁ ⨰ Σ₂)
L0-5 Σ₁ Σ₂ = runit[+][qty]< (⟨ 0 ⟩ ∷ Σ₁ ⨰ Σ₂) >

L0-7 : ∀ (s₁ s₂ : Sens) → (s₁ +[qty] s₂) ≡< qty ℕ > (s₂ +[qty] s₁)
L0-7 s₁ s₂ = commu[+]< s₁ , s₂ >


postulate
  sequentialComposition : ∀ {N} {γ₁ γ₂ : γ[ N ]} {τ₁ τ₂ : τ ᴢ} {e₂ : PTerm (ꜱ N)} (Σ′ : Σ[ N ]) (x₁ x₂ : 𝒟 𝓋)
    → (F₁ : ∀ v₁ → v₁ ∈support x₁ → ∃ 𝓋₂ ST v₁ ∷ γ₁ ⊢ e₂ ⇓ₚ 𝓋₂)
    → (F₂ : ∀ v₁ → v₁ ∈support x₂ → ∃ 𝓋₂ ST v₁ ∷ γ₂ ⊢ e₂ ⇓ₚ 𝓋₂)
    → (Σ₁ Σ₂ : Σₚ[ N ])
    → [𝒟]| x₁ - x₂ |≤ ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁)
    → (∀ (x : 𝓋)
    → (s₁ : x ∈support x₁)
    → (s₂ : x ∈support x₂)
    → ⊢ x ⦂ τ₁
    → ⊢ᴰ dπ₁ (F₁ x s₁) ⦂ τ₂
    → ⊢ᴰ dπ₁ (F₂ x s₂) ⦂ τ₂
    → [𝒟]| dπ₁ (F₁ x s₁) - dπ₁ (F₂ x s₂) |≤ ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₂))
    → ([𝒟]| bind-support x₁ (λ v₁ε → dπ₁ (F₁ (dπ₁ v₁ε) (dπ₂ v₁ε))) -
      bind-support x₂ (λ v₁ε → dπ₁ (F₂ (dπ₁ v₁ε) (dπ₂ v₁ε))) |≤
      ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ (Σ₁ +ⱽ Σ₂)))
  LTruncSep : ∀ {N} (p : Priv) → (Σ : Σ[ N ]) → [vec]⌉ Σ ⌈⸢ p ⸣ ≡ p ⨵ [vec]⌉ Σ ⌈⸢ one ⸣
  LVecScale : ∀ {N} (p : Priv)
    → (Σ′ Σ : Σ[ N ])
    → [vec]⌉ Σ′ ⌈⸢ ⟨ one ⟩ ⸣ ⨰ (p ⨵ [vec]⌉ Σ ⌈⸢ one ⸣) ≡ ([vec]⌉ Σ′ ⌈⸢ ⟨ one ⟩ ⸣ ⨰ ([vec]⌉ Σ ⌈⸢ one ⸣)) × p
  -- this is essentially saying p≤kp where 1≤k
  -- e^ ((⌉Σ′⌈¹ ⨰ Σ₁) + (⌉Σ₂ ⨰ Σ′⌈¹ × p)) × r
  -- ≤
  -- e^ ((⌉Σ′⌈¹ ⨰ Σ₁) + (⌉Σ′⌈¹ ⨰ ⌉Σ₂⌈¹) × p) × r
  L-P≤KP : ∀ {N r p} (Σ₁ :  Σₚ[ N ]) (Σ₂ Σ′ : Σ[ N ])
    →  (𝑒^ᴿ (p2r (((([vec]⌉ Σ′ ⌈⸢ ⟨ one ⟩ ⸣) ⨰ Σ₁)) +[qty] ((⌉ Σ₂ ⨰ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣) ×[qty] p))) × r )
    ≤ᵣ ((𝑒^ᴿ (p2r (([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] (([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ₂ ⌈⸢ ⟨ 1 ⟩ ⸣) ×[qty] p)) )) × r)

LPAPP : ∀ {N r p} → (Σ₁ :  Σₚ[ N ]) → ( Σ₂ Σ′ : Σ[ N ]) → (𝑒^ᴿ (p2r (((([vec]⌉ Σ′ ⌈⸢ ⟨ one ⟩ ⸣) ⨰ Σ₁) +[qty] ⟨ zero ⟩) +[qty] ((⌉ Σ₂ ⨰ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣) ×[qty] p))) × r ) ≤ᵣ ((𝑒^ᴿ (p2r (([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ₂ ⌈⸢ p ⸣)) )) × r)
LPAPP {r = r} {p = p} Σ₁ Σ₂ Σ′ rewrite (L0-4 (([vec]⌉ Σ′ ⌈⸢ ⟨ one ⟩ ⸣) ⨰ Σ₁))
  | LTruncSep p Σ₂
  | LVecScale p Σ′ Σ₂ = L-P≤KP {r = r} {p = p} Σ₁ Σ₂ Σ′

postulate
  L0-2 : ∀ (s : Sens) → ⟨ 0 ⟩ ×[qty] s ≡< qty ℕ > ⟨ 0 ⟩
  L0-6 : ∀ {N} (s : Sens) (Σ Σ′ : Σ[ N ]) → mapⱽ (_×[qty]_ s) Σ ⨰ Σ′ ≡ s ×[qty] (Σ ⨰ Σ′)
  L0-8 : ∀ (N : ℕ) → ⟨ ∣ N - N ∣ ⟩ ≡< qty ℕ > ⟨ 0 ⟩
  ▵ : ∀ {a b c d N : ℕ} {Σ₁ Σ₂ Σ₃ : Σ[ N ]} → ⟨ ∣ a - b ∣ ⟩ ≤ (Σ₁ ⨰ Σ₃) → ⟨ ∣ c - d ∣ ⟩ ≤ (Σ₂ ⨰ Σ₃) → ⟨ ∣ (a + c) - (b + d) ∣ ⟩ ≤ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L0-9 : ∀ {N} (Σ₁ Σ₂ Σ₃ : Σ[ N ]) → (Σ₁ ⨰ Σ₃) + (Σ₂ ⨰ Σ₃) ≡ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L-distrib-vec : ∀ {N} (Σ₁ Σ₂ Σ₃ : Σ[ N ]) → (Σ₁ ⨰ (Σ₂ + Σ₃)) ≡ (Σ₁ ⨰ Σ₂) + (Σ₁ ⨰ Σ₃)
  truncDichotomy : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → ([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ ⨰ Σ₂ ≡ ⟨ 0 ⟩) ∨ ([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ ⨰ Σ₂ ≡ `∞)
  -- should be straightforward by induction on x and γ₁/γ₂
  gammaVarValRel : ∀ {N} {γ₁ γ₂ : γ[ N ]} {Σ : Σ[ N ]} {ℾ : ℾ[ N ]} {x : idx N }
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧
    → (ε₁ : ⊢ γ₁ #[ x ] ⦂ ℾ #[ x ])
    → (ε₂ : ⊢ γ₂ #[ x ] ⦂ ℾ #[ x ])
    → ⟨ γ₁ #[ x ] , γ₂ #[ x ] ⟩∈𝒱′⟦ ℾ #[ x ] ː ε₁ , ε₂ ː Σ #[ x ] ⟧
  L2 : ∀ {N} (s : Sens) (Σ : Σ[ N ]) (τ : τ (ꜱ N)) → (substSx/τ s (⇧ᵗ (⇧ˢ Σ ⟨⟨ τ ⟩⟩))) ≡ (s ∷ Σ) ⟨⟨ τ ⟩⟩
  ▵× : ∀ {N} {r₁₁ r₁₂ r₂₁ r₂₂ : ℕ} {Σ₁ Σ₂ Σ′ : Σ[ N ]}
    → [vec]⌉ (Σ₁ + Σ₂) ⌈⸢ `∞ ⸣ ⨰ Σ′ ≡ ⟨ 0 ⟩
    → ⟨ ∣ r₁₁ - r₂₁ ∣ ⟩ ≤ (Σ₁ ⨰ Σ′)
    → ⟨ ∣ r₁₂ - r₂₂ ∣ ⟩ ≤ (Σ₂ ⨰ Σ′)
    → ⟨ ∣ r₁₁ ×ᴺ r₁₂ - r₂₁ ×ᴺ r₂₂ ∣ ⟩ ≡< qty ℕ > ⟨ 0 ⟩
  L3 : ∀ {N} {e e′₁ e′₂} {γ₁ γ₂ : γ[ N ]} {ℾ : ℾ[ N ]} {Γ₁ Γ₂} {Σ₁ : Σ[ N ]}
    → γ₁ ⊢ e ⇓ (sƛ⦂ e′₁ ∥ γ₁)
    → γ₂ ⊢ e ⇓ (sƛ⦂ e′₂ ∥ γ₂)
    → mapⱽ (instantiateΣ/τ Σ₁) Γ₁ ⊢ γ₁
    → mapⱽ (instantiateΣ/τ Σ₁) Γ₂ ⊢ γ₂
    → e′₁ ≡ e′₂ ∧ Γ₁ ≡ Γ₂
  L3′ : ∀ {N} {γ₁ γ₂ : γ[ N ]} {ℾ : ℾ[ N ]} {Γ} {Σ : Σ[ N ]}
    → mapⱽ (instantiateΣ/τ zero) Γ ⊢ γ₁
    → mapⱽ (instantiateΣ/τ zero) Γ ⊢ γ₂
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː mapⱽ (instantiateΣ/τ Σ) Γ ⟧
  -- DCD: got to here reviewing these
  L3′′ : ∀ {N} {γ₁ γ₂ : γ[ N ]} {ℾ : ℾ[ N ]} {Γ₁ Γ₂} {Σ₁ : Σ[ N ]}
    → ℾ ⊢ γ₁
    → ℾ ⊢ γ₂
    → mapⱽ (instantiateΣ/τ Σ₁) Γ₁ ⊢ γ₁
    → mapⱽ (instantiateΣ/τ Σ₁) Γ₂ ⊢ γ₂
    → Γ₁ ≡ Γ₂
  L4 : ∀ {N} (s₂ s₃ : Sens) (Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ Σ′ : Σ[ N ])
    → Σ₁ ⨰ Σ′ ≡ `∞
    → ([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ + ((s₂ ⨵ Σ₁₁) + Σ₂) ⊔ ((s₃ ⨵ Σ₁₂) + Σ₃)) ⨰ Σ′ ≡ `∞
  L5 : ∀ {N} {v₁ v₂ τ} {Σ : Σ[ N ]} → (ε₁ : ⊢ v₁ ⦂ Σ ⟨⟨ τ ⟩⟩)
    → (ε₂ : ⊢ v₂ ⦂ Σ ⟨⟨ τ ⟩⟩)
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ Σ ⟨⟨ τ ⟩⟩ ː ε₁ , ε₂ ː `∞ ⟧
  L6 : ∀ {N} (Σ′ : Σ[ N ]) (τ₂ τ₃ τ₁ : τ (ꜱ N))
    → ⇧ᵗ< ᴢ > (⇧ˢ Σ′ ⟨⟨ τ₂ ⟩⟩) ≡ instantiateΣ/τ 𝟎 τ₃
    → ⇧ᵗ< ᴢ > (⇧ˢ Σ′ ⟨⟨ τ₂ ⟩⟩) ≡ instantiateΣ/τ 𝟎 τ₁
    → τ₁ ≡ τ₃
  L7 : ∀ {N} (Σ′ : Σ[ N ]) (τ₃ τ₂ τ₁ : τ N)
    → (Σ′ ⟨⟨ τ₁ ⟩⟩) ≡ instantiateΣ/τ (𝐜< N > ⟨ 0 ⟩) τ₃
    → (Σ′ ⟨⟨ τ₁ ⟩⟩) ≡ instantiateΣ/τ (𝐜< N > ⟨ 0 ⟩) τ₂
    → τ₃ ≡ τ₂
  L8 : ∀ {N} {τ₁ ℾ Σ₀₀ Σ₀₁ Σ₁ Σ₂ τ₂ s sb} {e : Term (ꜱ N)}
    → ℾ , Σ₀₀ ⊢ sƛ⦂ τ₁ ∥ sb ⇒ e ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ₁ ] τ₂) , zero
    → ℾ , Σ₀₁ ⊢ sƛ⦂ τ₁ ∥ sb ⇒ e ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ₂ ] τ₂) , zero
    → Σ₁ ≡ Σ₂
  L9 : ∀ {N} → (Σ₂ Σ′ : Σ[ N ]) → (τ : τ (ꜱ N)) →  (Σ′ ⟨⟨ substΣ/τ ᴢ Σ₂ τ ⟩⟩) ≡ substSx/τ< ᴢ > (Σ₂ ⨰ Σ′) (⇧ᵗ< ᴢ > ((⟨ 0 ⟩ ∷ Σ′) ⟨⟨ τ ⟩⟩))
  typeSafety : ∀ {N} {e : Term N} {Γ : Γ[ N ]} {Σ Σ′ Σ₀ : Σ[ N ]} {v} {γ : γ[ N ]} {τ : τ N} → Γ , Σ₀ ⊢ e ⦂ τ , Σ → γ ⊢ e ⇓ v → ⊢ v ⦂ Σ′ ⟨⟨ τ ⟩⟩
  typeSafety₂ : ∀ {N} {e : PTerm N} {Γ : Γ[ N ]} {Σ : Σₚ[ N ]} {Σ′ Σ₀ : Σ[ N ]} {γ : γ[ N ]} {τ : τ N} {v} → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ → γ ⊢ e ⇓ₚ v → ⊢ᴰ v ⦂ (Σ′ ⟨⟨ τ ⟩⟩)
  subsumption : ∀ {N} {τ τ₁ τ₂ v₁ v₂ Σ′} {s₂ s₃ ε₁ ε₂ ε₃ ε₄} {Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ : Σ[ N ]}  → (τ₁ τ[⊔] τ₂) ≡ ⟨ τ ⟩
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ (Σ′ ⟨⟨ τ₁ ⟩⟩) ː ε₃ , ε₄ ː (s₂ ×[qty] ((Σ₁ ⨰ Σ′) +[qty] (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁₁)))) +[qty] (Σ₂ ⨰ Σ′)⟧
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ (Σ′ ⟨⟨ τ ⟩⟩) ː ε₁ , ε₂ ː (([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ + ((s₂ ⨵ Σ₁₁) + Σ₂) ⊔ ((s₃ ⨵ Σ₁₂) + Σ₃)) ⨰ Σ′)⟧
  -- essentially p ≤ N∞ + Np
  subsumption₂ : ∀ {N} {τ τ₁ τ₂ : τ N} {r₁ r₂} {p₂ p₃} {Σ′ Σ₁ Σ₁₁ Σ₁₂ : Σ[ N ]} {Σ₂ Σ₃ : Σₚ[ N ]}
    → r₁ ≤ᵣ (𝑒^ᴿ (p2r (((⌉ (Σ₁ ⨰ Σ′) + (Σ′ ⨰ Σ₁₁) ⌈⸢ ⟨ 1 ⟩ ⸣) ×[qty] p₂) +[qty] ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₂))) × r₂)
    → r₁ ≤ᵣ (𝑒^ᴿ (p2r ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ ([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ +ⱽ (([vec]⌉ Σ₁₁ ⌈⸢ p₂ ⸣ +ⱽ Σ₂) ⊔ⱽ ([vec]⌉ Σ₁₂ ⌈⸢ p₃ ⸣ +ⱽ Σ₃))))) × r₂)
  delayedΣEq : ∀ {N} {Γ : Γ[ N ]} {e₁ e′₂ τ₁ sx†₁ Σ₀₀ Σ₀₁ Σ₁ Σ′₁ τ₂ γ′ γ′₁ Γ₁ τ₁₁ τ₂₁ sb}
    → Γ , Σ₀₀ ⊢ e₁ ⦂ sƛ⦂ τ₁ ∥ sb ⇒[ ⟨ 0 ⟩ ∔ sx†₁ ∷ Σ₁ ] τ₂ , zero
    → γ′ ⊢ e₁ ⇓ (sƛ⦂ e′₂ ∥ γ′₁)
    → Γ₁ , Σ₀₁ ⊢ sƛ⦂ τ₁₁ ∥ sb ⇒ e′₂ ⦂ sƛ⦂ τ₁₁ ∥ sb ⇒[ ⟨ 0 ⟩ ∔ sx†₁ ∷ Σ′₁ ] τ₂₁ , zero
    → Σ₁ ≡ Σ′₁
  gammaDelayedΣEq : ∀ {N} {γ₁ γ₂ Σ′ ℾ Σ′′} {ℾ₁ : Γ[ N ]}
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′′ ː mapⱽ (instantiateΣ/τ Σ′′) ℾ₁ ⟧
    → Σ′ ≡ Σ′′
